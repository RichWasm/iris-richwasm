import { readFile } from "node:fs/promises";
import { loadRuntime, runStart } from "./host_common.ts";
import { instantiate } from "./instance.ts";

const rwExports = await loadRuntime();
const m = await instantiate(rwExports, await readFile("/dev/fd/0"), [], "the module");
runStart(m, rwExports, "the module");
