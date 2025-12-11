import type { Runtime } from "../../src/runtime/interface.d.ts";

function actually_set(
  table: Runtime["table"],
  instance: WebAssembly.Instance,
  index: number,
  value: number,
) {
  const diff = table.length - 1 - index;
  if (diff < 0) {
    table.grow(Math.abs(diff));
  }

  const funcName = `__rw_table_func_${value}`;
  const func = instance.exports[funcName];
  if (typeof func !== "function") {
    throw new TypeError(`Export ${funcName} is not a function`);
  }
  table.set(index, func);
}

export function mkTableset(table: Runtime["table"]) {
  let $instance: null | WebAssembly.Instance = null;

  const pending: { index: number; value: number }[] = [];

  function tableset(index: number, value: number) {
    if ($instance == null) {
      pending.push({ index, value });
    } else {
      actually_set(table, $instance, index, value);
    }
  }

  function flush(instance: WebAssembly.Instance) {
    if ($instance !== null) {
      throw new Error("tableset flush called more than once");
    }
    $instance = instance;

    for (const { index, value } of pending) {
      actually_set(table, $instance, index, value);
    }
  }

  return { tableset, flush };
}
