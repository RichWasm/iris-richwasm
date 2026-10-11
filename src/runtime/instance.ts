import { mkTableset } from "./tableset.ts";
import type { Runtime } from "./interface.d.ts";

export async function instantiateRuntime(bytes: BufferSource): Promise<Runtime> {
  const rw = await WebAssembly.instantiate(bytes);
  return rw.instance.exports as any as Runtime;
}

export async function instantiate(
  rwExports: Runtime,
  buf: Uint8Array,
  userImports: WebAssembly.ExportValue[],
  label: string,
): Promise<WebAssembly.Instance> {
  const module = await WebAssembly.compile(new Uint8Array(buf));
  const arity = WebAssembly.Module.imports(module).filter((i) => i.module === "").length;
  if (arity !== userImports.length) {
    throw new Error(`${label} has ${arity} imports but ${userImports.length} were linked`);
  }
  // HACK: tableset runs in the module's start function (before we have the
  // instance), so build it up front and flush into the instance afterward.
  const { tableset, flush } = mkTableset(rwExports.table);
  // NOTE: every user import is named ("", ""); the JS API reads imports in
  // order (one Get per import), so this hands them out by position.
  let next = 0;
  const imports: WebAssembly.Imports = {
    richwasm: { ...rwExports, tableset },
    "": new Proxy({}, { get: () => userImports[next++] }),
  };
  const instance = await WebAssembly.instantiate(module, imports);
  flush(instance);
  return instance;
}

export function lookupExport(
  instance: WebAssembly.Instance,
  name: string,
  label: string,
): WebAssembly.ExportValue {
  const exp = instance.exports[name];
  if (exp === undefined) {
    throw new Error(`${label} does not export \`${name}\``);
  }
  return exp;
}

export function callStart(instance: WebAssembly.Instance, label: string): unknown {
  const start = instance.exports._start;
  if (typeof start !== "function") {
    throw new Error(`Cannot find \`_start\` function in ${label}.`);
  }
  return start();
}
