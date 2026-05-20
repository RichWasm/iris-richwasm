import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { mkTableset } from "./tableset.ts";
import type { Runtime } from "../../src/runtime/interface.d.ts";
import { inspect } from "node:util";

const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");

// module1 -> fd 3, module2 -> fd 4, module3 -> fd 5
// (see Process_capture_three in src/support/process_utils.ml)
const [runtimeBuf, m1Buf, m2Buf, m3Buf] = await Promise.all([
  readFile(runtimePath),
  readFile("/dev/fd/3"),
  readFile("/dev/fd/4"),
  readFile("/dev/fd/5"),
]);

// A single richwasm runtime shared by all three modules: they must share one
// set of memories and one table so GC references can cross module boundaries.
const rw = await WebAssembly.instantiate(runtimeBuf);
const rwExports = rw.instance.exports as any as Runtime;

// Instantiate one richwasm module. `userImport`, if provided, satisfies the
// module's single ("", "") import -- a function exported by an upstream
// module. Each module registers its own functions into the shared table.
async function instantiate(
  buf: Uint8Array,
  userImport: WebAssembly.ExportValue | null,
): Promise<WebAssembly.Instance> {
  const { tableset, flush } = mkTableset(rwExports.table);
  const imports: WebAssembly.Imports = {
    richwasm: { ...rwExports, tableset },
  };
  if (userImport !== null) {
    imports[""] = { "": userImport };
  }
  // copy into a plain Uint8Array so the type satisfies `BufferSource`
  const { instance } = await WebAssembly.instantiate(
    new Uint8Array(buf),
    imports,
  );
  flush(instance);
  return instance;
}

// m1 (lin-lang) exports `add1`; m2 (glue) imports it and exports the wrapped
// `add1_wrapped`; m3 (mini-ml) imports that and runs `_start`.
const m1 = await instantiate(m1Buf, null);
const m2 = await instantiate(m2Buf, m1.exports.add1);
const m3 = await instantiate(m3Buf, m2.exports.add1_wrapped);

const start = m3.exports._start;
if (typeof start !== "function") {
  throw new Error("Cannot find `_start` function in module 3.");
}
const result = start();
process.stdout.write(inspect(result, { depth: null }));
