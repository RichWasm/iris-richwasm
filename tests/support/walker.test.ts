import * as assert from "node:assert/strict";
import { describe, it } from "node:test";
import { renderStart } from "./walker.ts";

const tag = (n: number): number => n << 1;

/**
 * A fresh pair of memories laid out like the runtime:
 * - gcmem page 0 is the root table, heap objects live at >= 65536
 * - mmmem has no root table
 * Each test gets its own so the cases stay isolated.
 *
 * @returns helpers for hand-building a heap:
 *  - `gc` / `mm`: DataViews over gcmem / mmmem
 *  - `mems`: the `{ gcmem, mmmem }` pair handed to `renderStart`
 *  - `w(view, byteAddr, val)`: write `val` as a little-endian 32-bit word
 *  - `gcRoot(base)`: register a heap object at `base`, returning its tagged root handle
 *  - `gcBare(base)`: the bare in-heap tagged gc pointer to `base`
 *  - `mmPtr(base)`: the tagged mm pointer to `base`
 */
function setup() {
  const gcmem = new WebAssembly.Memory({ initial: 2 });
  const mmmem = new WebAssembly.Memory({ initial: 1 });
  const gc = new DataView(gcmem.buffer);
  const mm = new DataView(mmmem.buffer);
  const mems = { gcmem, mmmem };
  const w = (view: DataView, byteAddr: number, val: number): void =>
    view.setUint32(byteAddr, val >>> 0, true);

  // Encode a gc *root handle* for a heap object at `base`: store the bare heap
  // pointer (base-1) in a fresh root slot, return the handle (slot-1).
  let nextSlot = 4;
  const gcRoot = (base: number): number => {
    const slot = nextSlot;
    nextSlot += 4;
    w(gc, slot, base - 1); // bare heap pointer (tagged gc)
    return slot - 1; // root handle (tagged gc)
  };
  const gcBare = (base: number): number => base - 1;
  const mmPtr = (base: number): number => base - 3;

  return { gc, mm, mems, w, gcRoot, gcBare, mmPtr };
}

describe("walker", () => {
  it("i31", () => {
    const { mems } = setup();
    assert.equal(renderStart(tag(42), "(I31)", mems), "42");
  });

  it("immutable struct box -> transparent tuple", () => {
    const { gc, mems, w, gcRoot } = setup();
    const base = 65536;
    w(gc, base + 0, tag(1));
    w(gc, base + 4, tag(2));
    assert.equal(
      renderStart(
        gcRoot(base),
        "((Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31)))))",
        mems,
      ),
      "(tup 1 2)",
    );
  });

  it("immutable variant box -> option/Some", () => {
    const { gc, mems, w, gcRoot } = setup();
    const base = 65552;
    w(gc, base + 0, 1); // discriminant: raw i32, NOT tagged
    w(gc, base + 4, tag(7)); // payload i31
    assert.equal(
      renderStart(
        gcRoot(base),
        "((Ref (Base GC) Imm (Variant ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))",
        mems,
      ),
      "(inj 1 7)",
    );
  });

  it("mutable cell (new 5) -> ref", () => {
    const { gc, mems, w, gcRoot } = setup();
    const base = 65568;
    w(gc, base + 0, tag(5));
    assert.equal(
      renderStart(gcRoot(base), "((Ref (Base GC) Mut (Ser I31)))", mems),
      "(ref 5)",
    );
  });

  it("mm (lin-lang) struct of raw i32", () => {
    const { mm, mems, w, mmPtr } = setup();
    const base = 16;
    w(mm, base + 0, 10);
    w(mm, base + 4, 20);
    assert.equal(
      renderStart(
        mmPtr(base),
        "((Ref (Base MM) Imm (Struct ((Ser (Num (Int I32))) (Ser (Num (Int I32)))))))",
        mems,
      ),
      "(tup 10 20)",
    );
  });

  it("nested struct, inner reached by a bare pointer", () => {
    const { gc, mems, w, gcRoot, gcBare } = setup();
    const outer = 65584;
    const inner = 65600;
    w(gc, outer + 0, gcBare(inner)); // field 0: bare in-heap pointer
    w(gc, outer + 4, tag(3)); // field 1: i31 3
    w(gc, inner + 0, tag(1));
    w(gc, inner + 4, tag(2));
    assert.equal(
      renderStart(
        gcRoot(outer),
        "((Ref (Base GC) Imm (Struct ((Ser (Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31))))) (Ser I31)))))",
        mems,
      ),
      "(tup (tup 1 2) 3)",
    );
  });

  it("lin-lang unboxed product -> multi-value return", () => {
    const { mems } = setup();
    assert.equal(
      renderStart(
        [1, 2, 3],
        "((Prod ((Ser (Num (Int I32))) (Ser (Num (Int I32))) (Ser (Num (Int I32))))))",
        mems,
      ),
      "(tup# 1 2 3)",
    );
  });

  it("unboxed sum: tag selects an arm, other arms' slots are skipped", () => {
    const { mems } = setup();
    // layout is `tag :: concat(all arms)`: tag 1, arm 0's slot, arm 1's value
    assert.equal(
      renderStart(
        [1, 0, 7],
        "((Sum ((Num (Int I32)) (Num (Int I32)))))",
        mems,
      ),
      "(inj# 1 7)",
    );
  });

  it("unboxed product inlined in a struct field", () => {
    const { gc, mems, w, gcRoot } = setup();
    const base = 65696;
    w(gc, base + 0, tag(1));
    w(gc, base + 4, tag(2));
    w(gc, base + 8, tag(3));
    assert.equal(
      renderStart(
        gcRoot(base),
        "((Ref (Base GC) Imm (Struct ((Ser (Prod ((Ser I31) (Ser I31)))) (Ser I31)))))",
        mems,
      ),
      "(tup (tup# 1 2) 3)",
    );
  });

  describe("mutable cell holding an immutable boxed pair", () => {
    const ty =
      "((Ref (Base GC) Mut (Ser (Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31)))))))";
    const cell = 65616;
    const inner = 65632;
    // Fresh memory with the cell -> boxed pair shape built in.
    const build = () => {
      const s = setup();
      s.w(s.gc, cell + 0, s.gcBare(inner)); // cell contents: bare ptr to the boxed pair
      s.w(s.gc, inner + 0, tag(1));
      s.w(s.gc, inner + 4, tag(2));
      return s;
    };

    it("renders the deref", () => {
      const { mems, gcRoot } = build();
      assert.equal(renderStart(gcRoot(cell), ty, mems), "(ref (tup 1 2))");
    });

    it("shows the cell address under showAddrs", () => {
      const { mems, gcRoot } = build();
      assert.equal(
        renderStart(gcRoot(cell), ty, mems, { showAddrs: true }),
        `(ref @gc:${cell} (tup 1 2))`,
      );
    });
  });

  it("boxed None whose unit payload aliases the variant", () => {
    const { gc, mems, w, gcRoot, gcBare } = setup();
    const v = 65760;
    w(gc, v + 0, 0); // tag 0 (None)
    w(gc, v + 4, gcBare(v)); // unit payload pointer aliases the variant itself
    assert.equal(
      renderStart(
        gcRoot(v),
        "((Ref (Base GC) Imm (Variant ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))",
        mems,
      ),
      "(inj 0)",
    );
  });

  it("recursive cons-list [1,2]", () => {
    const { gc, mems, w, gcRoot, gcBare } = setup();
    const v1 = 65792,
      c1 = 65808,
      v2 = 65824,
      c2 = 65840,
      v3 = 65856,
      empty = 65872;
    w(gc, v1 + 0, 1);
    w(gc, v1 + 4, gcBare(c1)); // cons
    w(gc, c1 + 0, tag(1));
    w(gc, c1 + 4, gcBare(v2)); // (1, tail)
    w(gc, v2 + 0, 1);
    w(gc, v2 + 4, gcBare(c2)); // cons
    w(gc, c2 + 0, tag(2));
    w(gc, c2 + 4, gcBare(v3)); // (2, tail)
    w(gc, v3 + 0, 0);
    w(gc, v3 + 4, gcBare(empty)); // nil
    const listTy =
      "((Rec (VALTYPE (Atom Ptr) GCRefs) (Ref (Base GC) Imm (Variant " +
      "((Ser (Ref (Base GC) Imm (Struct ()))) " +
      "(Ser (Ref (Base GC) Imm (Struct ((Ser I31) (Ser (Var 0)))))))))))";
    assert.equal(
      renderStart(gcRoot(v1), listTy, mems),
      "(inj 1 (tup 1 (inj 1 (tup 2 (inj 0)))))",
    );
  });
});
