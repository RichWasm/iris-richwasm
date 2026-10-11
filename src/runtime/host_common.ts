import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { renderStart } from "./walker.ts";
import { callStart, instantiateRuntime } from "./instance.ts";
import type { Runtime } from "./interface.d.ts";
import { inspect } from "node:util";

/** Instantiate the shared RichWasm runtime named by `RW_RUNTIME_WASM_PATH`. */
export async function loadRuntime(): Promise<Runtime> {
  const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
  assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");
  return instantiateRuntime(await readFile(runtimePath));
}

/**
 * Run a module's `_start` and write its result to stdout.
 *
 * Walker-rendered when `RW_START_TYPE` is set, else dumped raw.
 */
export function runStart(instance: WebAssembly.Instance, rwExports: Runtime, label: string): void {
  debugger;
  const result = callStart(instance, label);
  const startType = process.env.RW_START_TYPE;
  if (startType) {
    try {
      const showAddrs = process.env.RW_DEBUG_ADDRS === "1";
      process.stdout.write(renderStart(result, startType, rwExports, { showAddrs }));
    } catch (e) {
      // NOTE: fall back to a raw dump so a walker bug never silently corrupts a test.
      process.stderr.write(`walker error: ${(e as Error).stack ?? String(e)}\n`);
      process.stdout.write(inspect(result, { depth: null }));
    }
  } else {
    process.stdout.write(inspect(result, { depth: null }));
  }
}
