import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { loadRuntime, instantiate, lookupExport, runStart } from "./host_common.ts";

const [export1] = process.argv.slice(2);
assert.strict(export1, "host_double expects the module-1 export name as argv[2]");

const rwExports = await loadRuntime();
const [m1Buf, m2Buf] = await Promise.all([
  readFile("/dev/fd/3"), // m1: should export name specified by `export1`
  readFile("/dev/fd/4"), // m2: should import from m1; will use it's _start
]);

const m1 = await instantiate(rwExports, m1Buf, null);
const m2 = await instantiate(rwExports, m2Buf, lookupExport(m1, export1, "module 1"));
runStart(m2, rwExports, "module 2");
