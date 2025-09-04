# Design of the allocator and garbage collector

## Goals

We need an allocator powerful enough to manage interactions between two separate
regimes of memory management: one ought to be garbage collected, like Java or
ML, while the other ought to use a kind of static ownership discipline that
looks like ordinary malloc/free at run time.

The ABI should still pass arguments on the ordinary WebAssembly stack, however.

## Non-goals
We do not care if the GC and allocator are actually implemented, we just need
a spec: these things are really complicated, and in the end they are going to be
encapsulated behind a specification. The ABI should not dictate the use of
a particular allocator and collector, it should only rely on a specification.

## Challenges

In order to implement this...

## Why not use WasmGC?

The Wasm specification has a proposal, [WasmGC][1], describing a version of Wasm
with garbage collection that is supported by most major implementations of the
language. We found it inadequate for the following reasons...


[1]: https://github.com/WebAssembly/gc
