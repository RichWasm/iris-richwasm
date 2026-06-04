import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { mkTableset } from "./tableset.ts";
import { renderStart } from "./walker.ts";
import type { Runtime } from "../../src/runtime/interface.d.ts";
import { inspect } from "node:util";

const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");

const rwRuntime = readFile(runtimePath).then((x) => WebAssembly.instantiate(x));

const src = readFile("/dev/fd/0");
const [srcBuf, rw] = await Promise.all([src, rwRuntime]);

const rwExports = rw.instance.exports as any as Runtime;
// this is a massive HACK since tableset needs to run in the start function
// (before we have access to the instance)
const { tableset, flush } = mkTableset(rwExports.table);

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
  const startType = process.env.RW_START_TYPE;
  if (startType) {
    try {
      const showAddrs = process.env.RW_DEBUG_ADDRS === "1";
      process.stdout.write(renderStart(result, startType, rwExports, { showAddrs }));
    } catch (e) {
      // NOTE: we fall back to a raw dump so a walker bug never silently corrupts a test.
      process.stderr.write(`walker error: ${(e as Error).stack ?? String(e)}\n`);
      process.stdout.write(inspect(result, { depth: null }));
    }
  } else {
    process.stdout.write(inspect(result, { depth: null }));
  }
} else {
  throw new Error("Cannot find `_start` function.");
}
