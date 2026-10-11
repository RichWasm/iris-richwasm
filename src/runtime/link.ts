import { callStart, instantiate, lookupExport } from "./instance.ts";
import type { Runtime } from "./interface.d.ts";
import { renderStart } from "./walker.ts";

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

export interface RunSpec {
  modules: { name: string; startType?: string }[];
  links: Link[];
}

const raw = (value: unknown): string =>
  value === undefined ? "()" : Array.isArray(value) ? value.map(raw).join(" ") : String(value);

export async function runLinked(
  rw: Runtime,
  spec: RunSpec,
  wasms: Uint8Array[],
): Promise<{ typed: boolean; output: string }> {
  if (wasms.length !== spec.modules.length) {
    throw new Error(`${spec.modules.length} modules but ${wasms.length} binaries`);
  }
  const instances = await link(
    rw,
    spec.modules.map((m, i) => ({ name: m.name, wasm: wasms[i] })),
    spec.links,
  );
  const entries = spec.modules.filter((m) => instances.get(m.name)!.exports._start !== undefined);
  if (entries.length === 0) throw new Error("no module exports `_start`");
  if (entries.length > 1) {
    throw new Error(`several modules export \`_start\`: ${entries.map((m) => m.name).join(", ")}`);
  }
  const [{ name, startType }] = entries;
  const result = callStart(instances.get(name)!, `\`${name}\``);
  return startType === undefined
    ? { typed: false, output: raw(result) }
    : { typed: true, output: renderStart(result, startType, rw, { showAddrs: false }) };
}
