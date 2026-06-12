import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { mkTableset } from "./tableset.ts";
import { renderStart } from "./walker.ts";
import type { Runtime } from "../../src/runtime/interface.d.ts";
import { inspect } from "node:util";

/** Instantiate the shared RichWasm runtime named by `RW_RUNTIME_WASM_PATH`. */
export async function loadRuntime(): Promise<Runtime> {
  const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
  assert.strict(runtimePath, "RW_RUNTIME_WASM_PATH must be specified");
  const rw = await WebAssembly.instantiate(await readFile(runtimePath));
  return rw.instance.exports as any as Runtime;
}

/** Instantiate a RichWasm module; `userImport` satisfies its `("", "")` import if non-null. */
export async function instantiate(
  rwExports: Runtime,
  buf: Uint8Array,
  userImport: WebAssembly.ExportValue | null,
): Promise<WebAssembly.Instance> {
  // HACK: tableset runs in the module's start function (before we have the
  // instance), so build it up front and flush into the instance afterward.
  const { tableset, flush } = mkTableset(rwExports.table);
  const imports: WebAssembly.Imports = {
    richwasm: { ...rwExports, tableset },
  };
  if (userImport !== null) {
    imports[""] = { "": userImport };
  }
  const { instance } = await WebAssembly.instantiate(new Uint8Array(buf), imports);
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

/**
 * Run a module's `_start` and write its result to stdout.
 *
 * Walker-rendered when `RW_START_TYPE` is set, else dumped raw.
 */
export function runStart(instance: WebAssembly.Instance, rwExports: Runtime, label: string): void {
  const start = instance.exports._start;
  if (typeof start !== "function") {
    throw new Error(`Cannot find \`_start\` function in ${label}.`);
  }
  debugger;
  const result = start();
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
