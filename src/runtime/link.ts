import { instantiate, lookupExport } from "./instance.ts";
import type { Runtime } from "./interface.d.ts";

export interface LinkModule {
  name: string;
  wasm: Uint8Array;
}

export interface Link {
  importer: string;
  index: number;
  provider: string;
  export: string;
}

export async function link(
  rw: Runtime,
  modules: LinkModule[],
  links: Link[],
): Promise<Map<string, WebAssembly.Instance>> {
  const byName = new Map(modules.map((m) => [m.name, m]));
  const instances = new Map<string, WebAssembly.Instance>();
  const pending = new Set<string>();
  const visit = async (name: string): Promise<WebAssembly.Instance> => {
    const done = instances.get(name);
    if (done !== undefined) return done;
    const m = byName.get(name);
    if (m === undefined) throw new Error(`there is no module \`${name}\``);
    if (pending.has(name)) throw new Error(`\`${name}\` imports from itself through a cycle`);
    pending.add(name);
    const mine = links.filter((l) => l.importer === name).sort((a, b) => a.index - b.index);
    const values = [];
    for (const [i, l] of mine.entries()) {
      if (l.index !== i) throw new Error(`import ${i} of \`${name}\` is not linked`);
      values.push(lookupExport(await visit(l.provider), l.export, `\`${l.provider}\``));
    }
    const instance = await instantiate(rw, m.wasm, values, `\`${name}\``);
    pending.delete(name);
    instances.set(name, instance);
    return instance;
  };
  for (const m of modules) await visit(m.name);
  return instances;
}
