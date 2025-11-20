## Todo

### 2025-10-07

2 bump allocators:
- alloc -> bump allocator
- free -> noop
- register root -> bump allocator
- unregster root -> noop

Stil need to pp->rocq for annotated AST

Need to check if LL lx is less general than general inference.

fix free to temporarily save to reg

### 2025-10-14

- can just use nodejs to run -- v8 has wasm support -- WASI not needed
- existentials in locals? -- yes -> weakens env
- elab_type:
  - are size, mem, dropability propogated in MEMTYPE
  - how to find the kind of an Exists instruction?
- block type does in-fact need input
- clarification on LocalFx -> is the annotation the new locals or just the changes?
  - annotated is whole local ctx, unnanotated is a diff

Changes:
- mem to ser
- kind to rec
- extract subst_type, etc from rw.v
- add tables to env
- add functions to env
- add kind to fold
- modify unnanotated to have `Copy` vs `Move` for local.get and
- `Inject` and `New` should take `ConcreteMemory`

### 2025-11-13

A [WebAssembly.Instance][1], includes a JS object of exports, this *should* be able to be used as part of the [WebAssembly.instantiate][2] function's `importObject`.

Each RichWasm~>Wasm module should only include exports explicitly in the
RichWasm source.

This means we should be preserving export names.

[1]: https://developer.mozilla.org/en-US/docs/WebAssembly/Reference/JavaScript_interface/Instance
[2]: https://developer.mozilla.org/en-US/docs/WebAssembly/Reference/JavaScript_interface/instantiate_static
