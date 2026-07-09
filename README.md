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

## Differences between paper and mechanization
- Kinds are baked into the type syntax to allow the compiler access to them. These kinds are defined to be the most specific kinds, with subkinding allowed only in specific locations. Instruction types are also baked into instruction syntax.
- Function types: in the paper, a function type is `forall a*.xi`, where a* can be a list of quantifiers in any order. The mechanized syntax differs by ensuring that all `t:kappa` quantifiers are inner-most by stratifying functions types into `function_type` and `inner_function_type`. This was done to simplify flatenning and indexing (as type quantifiers can rely on previously declared variables).
- The live memory resource is named the "runtime token" and is appreviated `RT`.

## Important Files
This overview will focus on the most important files and folders, as it relates to the paper. 

### Language and Compiler.
`theories/syntax/rw.sig`: RichWasm syntax, using autosubst.

`theories/typing.v`: the type system.

`theories/typechecker/typechecker.v`: typechecker, not fully verified.

`theories/compiler`: the RichWasm to Wasm compiler.

### Model
`theories/iris/logrel.v`: the main logical relation. Line 1031 for type and closure interpretation. Line 1297 for instruction logical relation. Line 1377 for the module interpretation.

`theories/iris/memory.v`: memory model. Line 215 for the run time token.

`theories/iris/runtime.v`: runtime specifications

`theories/iris/language/cwp/def.v`: definition of weakest precondition modality.

### FTLR
`theories/iris/logrel/instr/typing.v`: statement of theorem 5.1

`theories/iris/logrel/instr/typing folder`: proofs of ABI compliance for each RichWasm instruction, supported by helper files in `theories/iris/logrel/instr folder`.

### Examples
`src` contains our case study compilers, and `tests` test case study + RichWasm compilers all together. `tests/e2e/main.ml` has the glue code and linking type examples.

`theories/examples`: the two proofs of linking with external Wasm.

## Our Admits
Aside from some instruction cases being admitted, we have the following admits:
- `theories/kinding_subst.v`: lemmas about kinding remaining true through a substitution, modulo the kind getting more specific
- `theories/iris/logrel/substitution.v`: lemmas related to the type interpretation remaining true through a substitution. Some pertinent cases were verified.
- `theories/iris/logrel/logrel_properties`: closure interpretation in an empty semantic environment implies closure interpretation in any semantic environment
- `theories/iris/logrel/function.v`: helper lemmas, mostly about representations

