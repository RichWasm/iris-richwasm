/*
 * Type-directed heap walker: reconstructs a type-erased RichWasm result into a
 * source-like S-expr by re-interpreting the live gcmem/mmmem under its type.
 *
 * The result type arrives as an S-expression in RW_START_TYPE; set
 * RW_DEBUG_ADDRS=1 to annotate each pointer with its memory + byte address.
 */

declare const __brand: unique symbol;
type Brand<T, B extends string> = T & { readonly [__brand]: B };

/** A raw 32-bit word as it sits on the stack / in a field / in a return slot. */
type Atom = Brand<number, "Atom">;
/** A *tagged* pointer atom (low bit set). */
type TaggedPtr = Brand<number, "TaggedPtr">;
/** A resolved, untagged byte offset into one specific memory. */
type ByteAddr = Brand<number, "ByteAddr">;

type MemName = "gc" | "mm";

const PTR_BIT = 0b01;
const GC_BIT = 0b10;
const WORD = 4;
const OFFSET: Readonly<Record<MemName, number>> = { gc: 1, mm: 3 };

type Classification = "int" | "ptr-mm" | "ptr-gc";

function classify(atom: Atom): Classification {
  if ((atom & PTR_BIT) === 0) return "int";
  return (atom & GC_BIT) === 0 ? "ptr-mm" : "ptr-gc";
}

function isTaggedPtr(atom: Atom): atom is TaggedPtr & Atom {
  return (atom & PTR_BIT) !== 0;
}

/** Reverse `compile_untag` (`n >>> 1`): the integer an i31 atom denotes. */
function untagI31(atom: Atom): number {
  return atom >>> 1;
}

//#region RichWasm type AST
// based off src/common/syntax.ml

type IntWidth = "I32" | "I64";
type FloatWidth = "F32" | "F64";
type NumType =
  | { num: "Int"; width: IntWidth }
  | { num: "Float"; width: FloatWidth };

type MemType =
  | { mem: "base"; base: "GC" | "MM" }
  | { mem: "var"; index: number };

type Mutability = "Mut" | "Imm";

/** Quantifier / Kind / Rep / Size are decoded loosely -- we only need them to
 * keep binder bookkeeping honest and to skip the right number of atoms. */
type Quantifier =
  | { q: "Memory" }
  | { q: "Representation" }
  | { q: "Size" }
  | { q: "Type"; kind: Sexp };

type RWType =
  | { t: "Var"; index: number }
  | { t: "I31" }
  | { t: "Num"; num: NumType }
  | { t: "Sum"; cases: RWType[] }
  | { t: "Variant"; cases: RWType[] }
  | { t: "Prod"; items: RWType[] }
  | { t: "Struct"; fields: RWType[] }
  | { t: "Ref"; mem: MemType; mut: Mutability; pointee: RWType }
  | { t: "CodeRef"; fn: Sexp }
  | { t: "Ser"; inner: RWType }
  | { t: "Plug"; rep: Sexp }
  | { t: "Span"; size: Sexp }
  | { t: "Rec"; kind: Sexp; body: RWType }
  | { t: "Exists"; quant: Quantifier; body: RWType };

//#endregion
//#region sexpr parser

type Sexp = string | Sexp[];

function parseSexp(input: string): Sexp {
  let i = 0;

  function skipWs(): void {
    while (i < input.length && /\s/.test(input[i]!)) i++;
  }

  function parseNode(): Sexp {
    skipWs();
    if (i >= input.length) throw new SexpError("unexpected end of input");
    const ch = input[i]!;
    if (ch === "(") {
      i++;
      const items: Sexp[] = [];
      for (;;) {
        skipWs();
        if (i >= input.length) throw new SexpError("unterminated list");
        if (input[i] === ")") {
          i++;
          return items;
        }
        items.push(parseNode());
      }
    }
    if (ch === ")") throw new SexpError("unexpected ')'");
    // atom: run of non-whitespace, non-paren characters
    const start = i;
    while (i < input.length && !/[\s()]/.test(input[i]!)) i++;
    return input.slice(start, i);
  }

  const node = parseNode();
  skipWs();
  if (i < input.length) throw new SexpError(`trailing input at ${i}`);
  return node;
}

class SexpError extends Error {}

function asList(s: Sexp, who: string): Sexp[] {
  if (typeof s === "string")
    throw new SexpError(`${who}: expected list, got atom ${s}`);
  return s;
}

function asAtom(s: Sexp, who: string): string {
  if (typeof s !== "string")
    throw new SexpError(`${who}: expected atom, got list`);
  return s;
}

/**
 * Head symbol + arguments of a `(Ctor arg...)` node. Bare atoms count as
 * nullary constructors.
 */
function ctor(s: Sexp): { head: string; args: Sexp[] } {
  if (typeof s === "string") return { head: s, args: [] };
  if (s.length === 0)
    throw new SexpError("empty list where constructor expected");
  return { head: asAtom(s[0]!, "ctor"), args: s.slice(1) };
}

//#endregion
//#region type decoder

function decodeNumType(s: Sexp): NumType {
  const { head, args } = ctor(s);
  if (head === "Int")
    return { num: "Int", width: asAtom(args[0]!, "Int") as IntWidth };
  if (head === "Float")
    return { num: "Float", width: asAtom(args[0]!, "Float") as FloatWidth };
  throw new SexpError(`bad NumType: ${head}`);
}

function decodeMem(s: Sexp): MemType {
  const { head, args } = ctor(s);
  if (head === "Base")
    return { mem: "base", base: asAtom(args[0]!, "Base") as "GC" | "MM" };
  if (head === "Var")
    return { mem: "var", index: Number(asAtom(args[0]!, "MemVar")) };
  throw new SexpError(`bad Memory: ${head}`);
}

function decodeQuantifier(s: Sexp): Quantifier {
  const { head, args } = ctor(s);
  switch (head) {
    case "Memory":
      return { q: "Memory" };
    case "Representation":
      return { q: "Representation" };
    case "Size":
      return { q: "Size" };
    case "Type":
      return { q: "Type", kind: args[0]! };
    default:
      throw new SexpError(`bad Quantifier: ${head}`);
  }
}

function decodeTypeList(s: Sexp): RWType[] {
  return asList(s, "type list").map(decodeType);
}

function decodeType(s: Sexp): RWType {
  const { head, args } = ctor(s);
  switch (head) {
    case "Var":
      return { t: "Var", index: Number(asAtom(args[0]!, "Var")) };
    case "I31":
      return { t: "I31" };
    case "Num":
      return { t: "Num", num: decodeNumType(args[0]!) };
    case "Sum":
      return { t: "Sum", cases: decodeTypeList(args[0]!) };
    case "Variant":
      return { t: "Variant", cases: decodeTypeList(args[0]!) };
    case "Prod":
      return { t: "Prod", items: decodeTypeList(args[0]!) };
    case "Struct":
      return { t: "Struct", fields: decodeTypeList(args[0]!) };
    case "Ref":
      return {
        t: "Ref",
        mem: decodeMem(args[0]!),
        mut: asAtom(args[1]!, "Mut") as Mutability,
        pointee: decodeType(args[2]!),
      };
    case "CodeRef":
      return { t: "CodeRef", fn: args[0]! };
    case "Ser":
      return { t: "Ser", inner: decodeType(args[0]!) };
    case "Plug":
      return { t: "Plug", rep: args[0]! };
    case "Span":
      return { t: "Span", size: args[0]! };
    case "Rec":
      return { t: "Rec", kind: args[0]!, body: decodeType(args[1]!) };
    case "Exists":
      return {
        t: "Exists",
        quant: decodeQuantifier(args[0]!),
        body: decodeType(args[1]!),
      };
    default:
      throw new SexpError(`unknown type constructor: ${head}`);
  }
}

/** Decode the `RW_START_TYPE` payload: an S-expr list of result types. */
export function decodeStartTypes(src: string): RWType[] {
  return decodeTypeList(parseSexp(src));
}

//#endregion
//#region value AST

type RWValue =
  | { kind: "int"; value: number | bigint }
  | { kind: "float"; value: number }
  | { kind: "tuple"; boxed: boolean; items: RWValue[] }
  | { kind: "variant"; boxed: boolean; tag: number; payload: RWValue }
  | {
      kind: "ref";
      mem: MemName;
      addr: ByteAddr;
      cellKey: string;
      target: RWValue;
    }
  | { kind: "closure"; index: number; env: RWValue[] }
  | { kind: "cycle"; ref: string }
  | { kind: "opaque"; note: string };

//#endregion
//#region Atom sources

interface Cursor {
  readonly rooted: boolean;
  nextAtom(): Atom;
  nextI32(): number;
  nextI64(): bigint;
  nextF32(): number;
  nextF64(): number;
}

function returnCursor(atoms: ReadonlyArray<number | bigint>): Cursor {
  let pos = 0;
  const num = (): number => {
    const v = atoms[pos++];
    if (typeof v === "bigint") return Number(v);
    if (typeof v !== "number")
      throw new WalkError(`missing return atom #${pos - 1}`);
    return v;
  };
  return {
    rooted: true,
    nextAtom: () => (num() | 0) as Atom,
    nextI32: () => num() | 0,
    nextI64: () => {
      const v = atoms[pos++];
      return typeof v === "bigint" ? v : BigInt(Math.trunc(Number(v)));
    },
    nextF32: num,
    nextF64: num,
  };
}

function memCursor(view: DataView, base: ByteAddr, startWord = 0): Cursor {
  let word = startWord;
  // Return the current byte address, then advance the word pointer by `n` so
  // stepping matches `arep_size` (1 word for ptr/i31/i32, 2 for i64/f64).
  const take = (n: number): number => {
    const a = base + word * WORD;
    word += n;
    return a;
  };
  return {
    rooted: false,
    nextAtom: () => (view.getUint32(take(1), true) | 0) as Atom,
    nextI32: () => view.getInt32(take(1), true),
    nextI64: () => {
      const lo = BigInt(view.getUint32(take(1), true));
      const hi = BigInt(view.getUint32(take(1), true));
      return lo | (hi << 32n);
    },
    nextF32: () => view.getFloat32(take(1), true),
    nextF64: () => view.getFloat64(take(2), true),
  };
}

//#endregion
//#region type var env

/** A bound type variable resolves either to a concrete type (with the env in
 * force at binding time) or to an abstract/existential witness we can't see. */
type Thunk = { abstract: true } | { abstract: false; type: RWType; env: TEnv };
interface TEnv {
  types: Thunk[];
}

const EMPTY_TENV: TEnv = { types: [] };

function pushType(env: TEnv, type: RWType, capturedAt: TEnv): TEnv {
  return { types: [{ abstract: false, type, env: capturedAt }, ...env.types] };
}

function pushAbstract(env: TEnv): TEnv {
  return { types: [{ abstract: true }, ...env.types] };
}

//#endregion
//#region walk ctx

interface Mems {
  gc: DataView;
  mm: DataView;
}

interface Ctx {
  mems: Mems;
  /** keys (`mem:addr`) currently on the deref stack -- back-edges are cycles. */
  onStack: Set<string>;
  /** keys that are the *target* of a back-edge, so the renderer labels them. */
  cycleIds: Map<string, number>;
  nextCycleId: { n: number };
  depthBudget: number;
}

class WalkError extends Error {}

function view(ctx: Ctx, mem: MemName): DataView {
  return mem === "gc" ? ctx.mems.gc : ctx.mems.mm;
}

/** Resolve a pointer atom to a concrete object base address, applying the gc
 * root indirection when the pointer came from the return/stack (`rooted`). */
function resolvePtr(
  atom: Atom,
  rooted: boolean,
  ctx: Ctx,
): { mem: MemName; base: ByteAddr } {
  const cls = classify(atom);
  if (cls === "int")
    throw new WalkError(`expected pointer, got int atom ${atom}`);
  if (cls === "ptr-mm") {
    return { mem: "mm", base: ((atom + OFFSET.mm) >>> 0) as ByteAddr };
  }
  if (rooted) {
    const slot = ((atom + OFFSET.gc) >>> 0) as ByteAddr;
    const heapPtr = (ctx.mems.gc.getUint32(slot, true) | 0) as Atom;
    return { mem: "gc", base: ((heapPtr + OFFSET.gc) >>> 0) as ByteAddr };
  }
  return { mem: "gc", base: ((atom + OFFSET.gc) >>> 0) as ByteAddr };
}

function unSer(t: RWType): RWType {
  return t.t === "Ser" ? t.inner : t;
}

/** Resolve a pointee type to its head memory form, following Ser/Rec/Exists/Var. */
function peelMem(t: RWType, env: TEnv): RWType {
  switch (t.t) {
    case "Ser":
      return peelMem(t.inner, env);
    case "Rec":
      return peelMem(t.body, pushType(env, t, env));
    case "Exists":
      return peelMem(t.body, pushAbstract(env));
    case "Var": {
      const th = env.types[t.index];
      return th && !th.abstract ? peelMem(th.type, th.env) : t;
    }
    default:
      return t;
  }
}

function assertNever(x: never, msg: string): never {
  throw new WalkError(`${msg}: ${JSON.stringify(x)}`);
}

//#endregion
//#region reconstruction

/** Reconstruct a *value-position* type by consuming atoms from `cur`. */
function fromStack(type: RWType, cur: Cursor, env: TEnv, ctx: Ctx): RWValue {
  switch (type.t) {
    case "I31":
      return { kind: "int", value: untagI31(cur.nextAtom()) };

    case "Num": {
      if (type.num.num === "Float") {
        return {
          kind: "float",
          value: type.num.width === "F32" ? cur.nextF32() : cur.nextF64(),
        };
      }
      return type.num.width === "I32"
        ? { kind: "int", value: cur.nextI32() }
        : { kind: "int", value: cur.nextI64() };
    }

    case "Prod":
      return {
        kind: "tuple",
        boxed: false,
        items: type.items.map((it) => fromStack(unSer(it), cur, env, ctx)),
      };

    case "Struct":
      // Structs are memory types; only reached on the stack via odd inputs.
      return {
        kind: "tuple",
        boxed: true,
        items: type.fields.map((f) => fromStack(unSer(f), cur, env, ctx)),
      };

    case "Sum":
      return fromStackSum(type.cases, cur, env, ctx);

    case "Variant":
      // Variants are memory types; in value position we can't lay them out, so
      // surface it rather than desync (consume its nominal width).
      for (let w = 0; w < atomWidth(type, env); w++) cur.nextAtom();
      return { kind: "opaque", note: "unboxed-variant" };

    case "Ref": {
      const atom = cur.nextAtom();
      return followRef(type, atom, cur.rooted, env, ctx);
    }

    case "CodeRef":
      return { kind: "closure", index: cur.nextAtom() >>> 0, env: [] };

    case "Rec":
      return fromStack(type.body, cur, pushType(env, type, env), ctx);

    case "Exists":
      return fromStack(type.body, cur, pushAbstract(env), ctx);

    case "Var": {
      const thunk = env.types[type.index];
      if (!thunk || thunk.abstract)
        return { kind: "opaque", note: `var${type.index}` };
      return fromStack(thunk.type, cur, thunk.env, ctx);
    }

    case "Ser":
      return fromStack(type.inner, cur, env, ctx);

    case "Plug":
      return { kind: "opaque", note: "plug" };
    case "Span":
      return { kind: "opaque", note: "span" };

    default:
      return assertNever(type, "fromStack");
  }
}

/** Unboxed sum: `tag :: concat(all arms)` (see `eval_rep`/`compile_inject`). We
 * read the tag, interpret the selected arm, and consume the remaining arm slots
 * to keep the cursor aligned. */
function fromStackSum(
  cases: RWType[],
  cur: Cursor,
  env: TEnv,
  ctx: Ctx,
): RWValue {
  const tag = cur.nextI32();
  let payload: RWValue = { kind: "tuple", boxed: false, items: [] };
  for (let i = 0; i < cases.length; i++) {
    if (i === tag) {
      payload = fromStack(unSer(cases[i]!), cur, env, ctx);
    } else {
      for (let w = 0; w < atomWidth(unSer(cases[i]!), env); w++) cur.nextAtom();
    }
  }
  return { kind: "variant", boxed: false, tag, payload };
}

/** Reconstruct a *memory-position* (pointee) type at `base` in `mem`. */
function fromMem(
  type: RWType,
  base: ByteAddr,
  mem: MemName,
  env: TEnv,
  ctx: Ctx,
): RWValue {
  const dv = view(ctx, mem);
  switch (type.t) {
    case "Struct": {
      const cur = memCursor(dv, base);
      return {
        kind: "tuple",
        boxed: true,
        items: type.fields.map((f) => fromStack(unSer(f), cur, env, ctx)),
      };
    }

    case "Variant": {
      const tag = dv.getInt32(base, true);
      const arm = type.cases[tag];
      if (!arm)
        return { kind: "opaque", note: `variant tag ${tag} out of range` };
      const payload = fromStack(unSer(arm), memCursor(dv, base, 1), env, ctx);
      return { kind: "variant", boxed: true, tag, payload };
    }

    case "Ser":
      return fromStack(type.inner, memCursor(dv, base), env, ctx);

    case "Rec":
      return fromMem(type.body, base, mem, pushType(env, type, env), ctx);

    case "Exists":
      return fromMem(type.body, base, mem, pushAbstract(env), ctx);

    case "Var": {
      const thunk = env.types[type.index];
      if (!thunk || thunk.abstract)
        return { kind: "opaque", note: `var${type.index}` };
      return fromMem(thunk.type, base, mem, thunk.env, ctx);
    }

    // A pointee that is itself a value type (e.g. `Ref ... I31`): read it as a
    // single serialized cell.
    default:
      return fromStack(type, memCursor(dv, base), env, ctx);
  }
}

/** Follow a `Ref` atom into the heap, with cycle detection. */
function followRef(
  refType: Extract<RWType, { t: "Ref" }>,
  atom: Atom,
  rooted: boolean,
  env: TEnv,
  ctx: Ctx,
): RWValue {
  if (!isTaggedPtr(atom)) {
    return { kind: "opaque", note: `non-ptr ${atom} where ref expected` };
  }

  // Zero-size pointees (empty struct or prod) are allocated with `alloc(0)`,
  // which doesn't advance the bump pointer, so they alias whatever is allocated
  // next -- often their own container. They hold no data and no identity, so
  // never dereference them: doing so yields spurious cycles.
  const peeled = peelMem(refType.pointee, env);
  if (
    (peeled.t === "Struct" && peeled.fields.length === 0) ||
    (peeled.t === "Prod" && peeled.items.length === 0)
  ) {
    const unit: RWValue = {
      kind: "tuple",
      boxed: peeled.t === "Struct",
      items: [],
    };
    if (refType.mut === "Imm") return unit;
    const z = resolvePtr(atom, rooted, ctx);
    return {
      kind: "ref",
      mem: z.mem,
      addr: z.base,
      cellKey: `${z.mem}:${z.base}`,
      target: unit,
    };
  }

  const { mem, base } = resolvePtr(atom, rooted, ctx);
  const key = `${mem}:${base}`;

  if (ctx.onStack.has(key)) {
    if (!ctx.cycleIds.has(key)) ctx.cycleIds.set(key, ctx.nextCycleId.n++);
    return { kind: "cycle", ref: key };
  }
  if (ctx.depthBudget <= 0) return { kind: "opaque", note: "max-depth" };

  ctx.onStack.add(key);
  ctx.depthBudget--;
  try {
    const target = fromMem(refType.pointee, base, mem, env, ctx);
    // An *immutable* ref to a struct/variant is the compiler's boxing of a
    // tuple/sum, not a source-level `ref` cell -- render it transparently.
    // Mutable refs (`new`) are real cells and keep the `(ref ...)` wrapper.
    if (
      refType.mut === "Imm" &&
      (target.kind === "tuple" || target.kind === "variant")
    ) {
      return target;
    }
    return { kind: "ref", mem, addr: base, cellKey: key, target };
  } finally {
    ctx.depthBudget++;
    ctx.onStack.delete(key);
  }
}

/** Number of stack atoms a value type occupies (mirrors `eval_rep` widths). */
function atomWidth(type: RWType, env: TEnv): number {
  switch (type.t) {
    case "I31":
    case "Ref":
    case "CodeRef":
      return 1;
    case "Num":
      return type.num.width === "I64" || type.num.width === "F64" ? 2 : 1;
    case "Prod":
      return type.items.reduce((n, it) => n + atomWidth(unSer(it), env), 0);
    case "Struct":
      return type.fields.reduce((n, f) => n + atomWidth(unSer(f), env), 0);
    case "Sum":
      return 1 + type.cases.reduce((n, c) => n + atomWidth(unSer(c), env), 0);
    case "Rec":
      return atomWidth(type.body, pushType(env, type, env));
    case "Exists":
      return atomWidth(type.body, pushAbstract(env));
    case "Ser":
      return atomWidth(type.inner, env);
    case "Var": {
      const thunk = env.types[type.index];
      return thunk && !thunk.abstract ? atomWidth(thunk.type, thunk.env) : 1;
    }
    case "Variant":
    case "Plug":
    case "Span":
      return 1;
    default:
      return assertNever(type, "atomWidth");
  }
}

//#endregion
//#region rendering

interface RenderOpts {
  showAddrs: boolean;
}

function render(value: RWValue, ctx: Ctx, opts: RenderOpts): string {
  switch (value.kind) {
    case "int":
      return String(value.value);
    case "float":
      return String(value.value);
    case "tuple": {
      const head = value.boxed ? "tup" : "tup#";
      return value.items.length === 0
        ? `(${head})`
        : `(${head} ${value.items.map((v) => render(v, ctx, opts)).join(" ")})`;
    }
    case "variant": {
      const head = value.boxed ? "inj" : "inj#";
      return value.payload.kind === "tuple" && value.payload.items.length === 0
        ? `(${head} ${value.tag})`
        : `(${head} ${value.tag} ${render(value.payload, ctx, opts)})`;
    }
    case "ref": {
      const label = ctx.cycleIds.has(value.cellKey)
        ? `#${ctx.cycleIds.get(value.cellKey)}=`
        : "";
      const addr = opts.showAddrs ? `@${value.mem}:${value.addr} ` : "";
      return `(ref ${label}${addr}${render(value.target, ctx, opts)})`;
    }
    case "closure":
      return `(closure #${value.index})`;
    case "cycle":
      return `#${ctx.cycleIds.get(value.ref) ?? "?"}`;
    case "opaque":
      return `<${value.note}>`;
    default:
      return assertNever(value, "render");
  }
}

//#endregion
//#region entry point

/**
 * Render the result of `_start` structurally.
 *
 * @param result    the JS value returned by `instance.exports._start()`
 *                  (a number, a bigint, or an array of them for multi-value).
 * @param startType the `RW_START_TYPE` S-expression (list of result types).
 * @param mems      the gc/mm memories (the runtime instance's exports).
 */
export function renderStart(
  result: unknown,
  startType: string,
  mems: { gcmem: WebAssembly.Memory; mmmem: WebAssembly.Memory },
  opts?: Partial<RenderOpts>,
): string {
  const types = decodeStartTypes(startType);
  const atoms: Array<number | bigint> =
    result === undefined || result === null
      ? []
      : Array.isArray(result)
        ? result
        : [result as number | bigint];

  const ctx: Ctx = {
    mems: {
      gc: new DataView(mems.gcmem.buffer),
      mm: new DataView(mems.mmmem.buffer),
    },
    onStack: new Set(),
    cycleIds: new Map(),
    nextCycleId: { n: 1 },
    depthBudget: 512,
  };
  const renderOpts: RenderOpts = { showAddrs: opts?.showAddrs ?? false };

  const cur = returnCursor(atoms);
  const values = types.map((t) => fromStack(t, cur, EMPTY_TENV, ctx));

  if (values.length === 0) return "()";
  const body =
    values.length === 1
      ? render(values[0]!, ctx, renderOpts)
      : `(tup# ${values.map((v) => render(v, ctx, renderOpts)).join(" ")})`;
  return body;
}
