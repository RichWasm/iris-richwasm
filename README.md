# Iris-RichWasm

This is a formalization of RichWasm in Iris based on Iris-Wasm.

## Building

Install the dependencies using opam:

```bash
opam switch create iris-richwasm 4.14.2
opam switch link iris-richwasm .
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only vendor/iriswasm .
```

Then you can build the project with Dune:

```bash
dune build
```

## Additional Dependencies

The cli and certain tests require `wabt` (WebAssembly Binary Toolkit) to
convert between the produced binary and WebAssembly text format.

