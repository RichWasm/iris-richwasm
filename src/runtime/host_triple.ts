import * as assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { loadRuntime, instantiate, lookupExport, runStart } from "./host_common.ts";

const [export1, export2] = process.argv.slice(2);
assert.strict(export1, "host_triple expects the module-1 export name as argv[2]");
assert.strict(export2, "host_triple expects the module-2 export name as argv[3]");

const rwExports = await loadRuntime();
const [m1Buf, m2Buf, m3Buf] = await Promise.all([
  readFile("/dev/fd/3"), // m1: should export name specified by `export1`
  readFile("/dev/fd/4"), // m2: should import from m1, export name specified by `export2`
  readFile("/dev/fd/5"), // m3: should import from m2; will use its _start
]);

const m1 = await instantiate(rwExports, m1Buf, null);
const m2 = await instantiate(rwExports, m2Buf, lookupExport(m1, export1, "module 1"));
const m3 = await instantiate(rwExports, m3Buf, lookupExport(m2, export2, "module 2"));
runStart(m3, rwExports, "module 3");
