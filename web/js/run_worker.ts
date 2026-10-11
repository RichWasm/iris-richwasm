import { instantiateRuntime } from "../../src/runtime/instance.ts";
import { runLinked } from "../../src/runtime/link.ts";

const runtime = fetch("./richwasm.wasm").then((r) => r.arrayBuffer());

self.onmessage = async (event: MessageEvent<{ spec: string; wasms: Uint8Array[] }>) => {
  const { spec, wasms } = event.data;
  try {
    const rw = await instantiateRuntime(await runtime);
    self.postMessage(await runLinked(rw, JSON.parse(spec), wasms));
  } catch (e) {
    self.postMessage({ error: e instanceof Error ? e.message : String(e) });
  }
};
