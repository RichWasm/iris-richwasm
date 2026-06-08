import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { mkTableset } from "./tableset.ts";
import type { Runtime } from "../../src/runtime/interface.d.ts";
import { inspect } from "node:util";

const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");

// Link names (argv): module 1 exports `export1`, module 2 exports `export2`.
const [export1, export2] = process.argv.slice(2);
assert.strict(export1, "host_triple expects the module-1 export name as argv[2]");
assert.strict(export2, "host_triple expects the module-2 export name as argv[3]");

// module1 -> fd 3, module2 -> fd 4, module3 -> fd 5
// (see Process_capture_three in src/support/process_utils.ml)
const [runtimeBuf, m1Buf, m2Buf, m3Buf] = await Promise.all([
  readFile(runtimePath),
  readFile("/dev/fd/3"),
  readFile("/dev/fd/4"),
  readFile("/dev/fd/5"),
]);

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
  const { instance } = await WebAssembly.instantiate(
    new Uint8Array(buf),
    imports,
  );
  flush(instance);
  return instance;
}

function lookupExport(
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

// m2 imports m1's `export1`, m3 imports m2's `export2`, then m3 runs `_start`.
const m1 = await instantiate(m1Buf, null);
const m2 = await instantiate(m2Buf, lookupExport(m1, export1, "module 1"));
const m3 = await instantiate(m3Buf, lookupExport(m2, export2, "module 2"));

const start = m3.exports._start;
if (typeof start !== "function") {
  throw new Error("Cannot find `_start` function in module 3.");
}
const result = start();
process.stdout.write(inspect(result, { depth: null }));
