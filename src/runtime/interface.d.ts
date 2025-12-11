export interface Runtime {
  tablenext: number;
  table: WebAssembly.Table;
  mmmem: WebAssembly.Memory;
  gcmem: WebAssembly.Memory;
  registerroot(address: number): number;
  unregisterroot(address: number): number;
  mmalloc(bytes: number): number;
  gcalloc(bytes: number): number;
  free(address: number): void;
  setflag(a: number, b: number, c: number): void;
}

export interface FullRuntime extends Runtime {
  tableset(index: number, func: number): void;
}
