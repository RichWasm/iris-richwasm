import { readFile } from "node:fs/promises";
import { resolve } from "node:path";

interface Runtime {
  tablenext: number;
  table: WebAssembly.Table;
  mmmem: WebAssembly.Memory;
  gcmem: WebAssembly.Memory;
  registerroot: (address: number) => number;
  unregisterroot: (address: number) => number;
  mmalloc: (bytes: number) => number;
  gcalloc: (bytes: number) => number;
  tableset: (idx: number, f: Function) => void;
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

console.log("mmalloc tests, allocate 4, 4, 1, 2");
console.log([
  runtime.mmalloc(4),
  runtime.mmalloc(4),
  runtime.mmalloc(1),
  runtime.mmalloc(2),
]);
console.log("mmmem size", runtime.mmmem.buffer.byteLength);
console.log("mmalloc 16384 (one whole page)");
console.log(runtime.mmalloc(16384));

const mmSize = runtime.mmmem.buffer.byteLength;
console.log("mmmem size", mmSize);
console.log("---");

console.log("original gcmem size", runtime.gcmem.buffer.byteLength);
console.log("gcalloc 4", runtime.gcalloc(4));
console.log("gcmem size", runtime.gcmem.buffer.byteLength);

console.log("gcalloc tests, allocate 4, 1, 2");
console.log([runtime.gcalloc(4), runtime.gcalloc(1), runtime.gcalloc(2)]);
console.log("gcmem size", runtime.gcmem.buffer.byteLength);
console.log("gcalloc 65536 (four pages)");
console.log(runtime.gcalloc(65536));
console.log("gcmem size", runtime.gcmem.buffer.byteLength);
console.log("---");

console.log(
  "make sure mmmem hasn't changed when working with gc:",
  runtime.mmmem.buffer.byteLength == mmSize
);
console.log("---");

console.log("registerroot: numbers should just incrememnt by 4");
console.log([
  runtime.registerroot(46436),
  runtime.registerroot(459),
  runtime.registerroot(1),
  runtime.registerroot(5),
]);
console.log("---");

console.log("tableset");
console.log("set index 1, check length");
runtime.tableset(1, runtime.free);
console.log(runtime.table.length);
console.log("set index 0, check length");
runtime.tableset(0, runtime.setflag);
console.log(runtime.table.length);
console.log("now set index 8");
runtime.tableset(8, runtime.gcalloc);
console.log(runtime.table.length);

console.log("index 8 should be gcalloc, call it (ptr should be >100k)");
console.log(runtime.table.get(8)(4));
console.log("---");

console.log("make sure free, setflag, and unregisterroot don't trap");
runtime.free(0);
runtime.unregisterroot(0);
runtime.setflag(0, 1, 2);
console.log("---");
