# Iris-RichWasm

This is a formalization of RichWasm in Iris based on Iris-Wasm.

## Setup

This is a Rocq and Ocaml hybrid workspace managed by dune.

### Dependencies

Firstly, ensure you have the required system dependencies:
- `opam`
- `wabt` (WebAssembly Binary Toolkit)

Alternativly there is a nix flake availble.

### Opam

Install the dependencies using opam:

```bash
opam switch create iris-richwasm 4.14.2
opam switch link iris-richwasm .
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```

## Usage

### Build

Then you can build the project with Dune:

```bash
dune build
```

This includes all the Rocq proofs, so this may take a while.

### Tests

Run both unit tests and end to end tests with:

```bash
dune test
```

### Cli

There is also a CLI availble

(OWEN TODO)

## Structure


(OWEN TODO)

```
.
├── bin/ -- cli
├── src/
│   ├── common/
│   ├── lin-lang/
│   ├── mini-ml/
├── tests
│   ├── e2e
│   ├── examples
│   ├── lin-lang
│   ├── main.ml
│   ├── mini-ml
│   ├── richwasm
│   ├── runtime
│   └── support
├── theories/
│   ├── compiler
│   ├── dune
│   ├── examples
│   ├── extract
│   ├── iris
│   ├── kinding_subst.v
│   ├── layout.v
│   ├── named_props
│   ├── opsem
│   ├── prelude.v
│   ├── syntax
│   ├── syntax.v
│   ├── typechecker
│   ├── typing.v
│   ├── util.v
│   └── wasm
```

