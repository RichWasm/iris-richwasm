import { readFile } from "node:fs/promises";
import { loadRuntime } from "./host_common.ts";
import { runLinked, type RunSpec } from "./link.ts";

const spec: RunSpec = JSON.parse(process.argv[2]);
const wasms = await Promise.all(spec.modules.map((_, i) => readFile(`/dev/fd/${3 + i}`)));
const { output } = await runLinked(await loadRuntime(), spec, wasms);
process.stdout.write(output);
