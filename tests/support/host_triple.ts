import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { mkTableset } from "./tableset.ts";
import type { Runtime } from "../../src/runtime/interface.d.ts";
import { inspect } from "node:util";

const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");

const [runtimeBuf, module1Buf, glueBuf, module2Buf] = Promise.all([
  readFile(runtimePath),
  // TODO: can we use /dev/fd/...
  readFile(3),
  readFile(4),
  readFile(5),
])

const rwRuntime = WebAssembly.instantiate(runtimeBuf);
const rwExports = rw.instance.exports as any as Runtime;
// TODO:
/* const { tableset, flush } = mkTableset(rwExports.table);

const module = await WebAssembly.instantiate(srcBuf, {
  richwasm: { ...rwExports, tableset },
});
flush(module.instance);
if (
  "_start" in module.instance.exports &&
  typeof module.instance.exports._start === "function"
) {
  debugger;
  const result = module.instance.exports._start();
  process.stdout.write(inspect(result, { depth: null }));
} else {
  throw new Error("Cannot find `_start` function.");
} */
