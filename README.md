# Iris-RichWasm

This is a formalization of RichWasm in Iris based on Iris-Wasm.

## Setup

This is a Rocq and OCaml hybrid workspace managed by dune.

### Dependencies

Firstly, ensure you have the required system dependencies:
- `opam`
- `wabt` (WebAssembly Binary Toolkit) -- the tests and the CLI shell out to `wat2wasm`/`wasm2wat`
- Node.js (tested with v24) -- runs the runtime for the end-to-end tests and the `run` subcommand
- `just` (optional) -- shortcuts for the common commands below

Alternatively there is a nix flake available: `nix develop` enters a shell with all dependencies, `nix build` builds everything, and `nix flake check` builds and runs the tests.

### Opam

Install the dependencies using opam:

```bash
opam switch create iris-richwasm 4.14.2
opam switch link iris-richwasm .
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```

The last step installs dune (3.23+ is required) along with the Rocq and OCaml dependencies; OCaml 4.14 is required by some of them.

## Usage

### Build

Then you can build the project with `just build`, or directly with Dune:

```sh
dune build
```

This includes all the Rocq proofs, so this may take a while.

### Tests

Run both unit tests and end to end tests with `just test`, or:

```sh
dune test
```

### CLI

There is also a CLI exposing the compiler pipeline, invoked as `just cli <subcommand>` (an alias for `dune exec bin/main.exe -- <subcommand>`):

- `mml2rw <file>` -- compile a MiniML module to RichWasm
- `ll2rw <file>` -- compile a LinLang module to RichWasm
- `rw-elab <file>` -- elaborate a RichWasm module (sexp) with full type annotations
- `rw2wasm <file>` -- typecheck a RichWasm module (sexp) and compile it to WebAssembly (wat)
- `run <file>` -- like `rw2wasm`, then assemble with `wat2wasm` and execute on the runtime

Every subcommand reads the given file, or stdin if the argument is `-` or omitted. `mml2rw`, `ll2rw`, and `rw-elab` accept `-pp {pp|sexp|rocq}` to select the output format and `-elab {true|false}` (default `true`) to toggle elaboration of the output.

`rw2wasm` and `run` use the typechecker and compiler extracted from the Rocq development.

For example:

```sh
# pretty-print the compiled RichWasm
$ just cli ll2rw tests/examples/standalone/safe_div.ll
# run the safe_div with the RichWasm runtime
$ just cli run tests/examples/standalone/safe_div.rw
0
```

(`safe_div.rw` is `ll2rw -pp sexp -elab false` applied to `safe_div.ll`; dividing by zero takes the error branch, which the caller maps to `0`.)

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

