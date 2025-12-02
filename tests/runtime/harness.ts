import { readFile } from "node:fs/promises";
import { resolve } from "node:path";

interface Runtime {
  tablenext: number;
  mmmem: WebAssembly.Memory;
  gcmem: WebAssembly.Memory;
  registerroot: (address: number) => number;
  unregisterroot: (address: number) => number;
  mmalloc: (bytes: number) => number;
  gcalloc: (bytes: number) => number;
  tableset: (idx: number, f: number) => void;
  free: (address: number) => void;
  setflag: (a: number, b: number, c: number) => void;
}

const WASM_PATH = resolve(
  import.meta.url.slice(5),
  "..",
  "..",
  "..",
  "src",
  "runtime",
  "richwasm.wasm"
);

const wasm = await readFile(WASM_PATH);
const { instance } = await WebAssembly.instantiate(wasm, {});

const runtime = instance.exports as unknown as Runtime;

console.log([
  runtime.mmalloc(4),
  runtime.mmalloc(4),
  runtime.mmalloc(1),
  runtime.mmalloc(2),
]);

console.log([
  runtime.gcalloc(4),
  runtime.gcalloc(4),
  runtime.gcalloc(1),
  runtime.gcalloc(2),
]);

console.log([
  runtime.registerroot(4),
  runtime.registerroot(4),
  runtime.registerroot(1),
  runtime.registerroot(2),
]);
