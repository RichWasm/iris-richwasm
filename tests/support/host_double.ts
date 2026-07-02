import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { loadRuntime, instantiate, lookupExport, runStart } from "./host_common.ts";

const [providerExport, entryArg] = process.argv.slice(2);
assert.strict(providerExport, "host_double expects the provider export name as argv[2]");
const entry = entryArg ? Number(entryArg) : 2;
assert.strict(entry === 1 || entry === 2, "host_double entry (argv[3]) must be 1 or 2");

const rwExports = await loadRuntime();
const bufs = await Promise.all([
  readFile("/dev/fd/3"), // m1
  readFile("/dev/fd/4"), // m2
]);

// provider (the non-entry module) is instantiated first; the entry imports it
const providerIdx = entry === 2 ? 1 : 2;
const provider = await instantiate(rwExports, bufs[providerIdx - 1], null);
const entryInst = await instantiate(
  rwExports,
  bufs[entry - 1],
  lookupExport(provider, providerExport, `module ${providerIdx}`),
);
runStart(entryInst, rwExports, `module ${entry}`);
