import { readFile } from "node:fs/promises";
import { loadRuntime, instantiate, runStart } from "./host_common.ts";

const rwExports = await loadRuntime();
const m = await instantiate(rwExports, await readFile("/dev/fd/0"), null);
runStart(m, rwExports, "the module");
