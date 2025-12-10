// @ts-check
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const runtimePath = process.env.RW_RUNTIME_WASM_PATH;
assert(runtimePath, 'RW_RUNTIME_WASM_PATH must be specified');

const rwRuntime = readFile(runtimePath).then(WebAssembly.instantiate);

const src = readFile('/dev/fd/0');
const [srcBuf, rw] = await Promise.all([src, rwRuntime]);
const module = await WebAssembly.instantiate(srcBuf, { richwasm: rw.instance.exports });
if ('_start' in module.exports && typeof module.exports._start === 'function') {
	console.dir(module.exports._start());
} else {
  throw new Error('Cannot find `_start` function.');
}
