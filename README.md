# Iris-RichWasm

This is a formalization of RichWasm in Iris based on Iris-Wasm.

## Setup (Kick-the-tires)

This is a Rocq and OCaml hybrid workspace managed by the dune build system. There are several options for installing the codebase:
1. Docker image
2. VM image
3. Nix
4. Installing from scratch

### 3. Nix
The flake also builds a Docker image of the `nix develop` shell with a copy of this repository. Build and start it with these commands, using `aarch64-linux` on ARM:

```sh
nix build .#packages.x86_64-linux.docker
docker load < result
docker run -it --name richwasm -p 8000:8000 iris-richwasm
```

The shell starts in `~/iris-richwasm` with everything `nix develop` provides, so the commands below work there. The image adds neovim, emacs, nano, git, and python3. `-p 8000:8000` lets your browser reach the web demo's server (see Web demo). After you exit, `docker start -ai richwasm` gets back into the same container.

### 4. Installing from scratch

#### Dependencies

Firstly, ensure you have the required system dependencies:
- `opam`
- `wabt` ([WebAssembly Binary Toolkit](https://github.com/webassembly/wabt) — the tests and the CLI shell out to `wat2wasm`/`wasm2wat`
- Node.js ([tested with v24](https://nodejs.org/en) — runs the runtime for the end-to-end tests and the `run` subcommand
- `just` (optional) -- shortcuts for the common commands below

Alternatively there is a nix flake available: `nix develop` enters a shell with all dependencies, `nix build` builds everything, and `nix flake check` builds and runs the tests.

#### Opam

Install the dependencies using opam:

```bash
opam switch create iris-richwasm 4.14.2
opam switch link iris-richwasm .
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```

The last step installs dune (3.23+ is required) along with the Rocq and OCaml dependencies; OCaml 4.14 is required by some of them.


### Build

After installation, you can build the project with `just build`, or directly with Dune:

```sh
dune build
```

This includes all the Rocq proofs, so this may take a while. The build process will have warnings regarding notations already being used in scope `subst_scope` and an opacity warning, which are expected and can be ignored. We have included a `Print Assumptions` command in `theories/iris/logrel/instr/typing.v` for `Theorem fundamental_typing`. The expected output for this command is the following:

```
Section Variables:
Σ: gFunctors
wasmG0: wasmG Σ
sr: store_runtime
rti: rt_invariant Σ
richwasmG0: richwasmG Σ
mr: module_runtime
logrel_na_invs0: logrel_na_invs Σ
Axioms:
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec :
  ∀ P : nat → Prop,
    (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
FunctionalExtensionality.functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```

### Tests

Run both unit tests and end to end tests with `just test`, or:

```sh
dune test
```
The expected output is all tests succeeding with `[OK]`.

**At this point, Kick-the-tires is concluded.**

## Usage

### CLI

There is also a CLI exposing the compiler pipeline, invoked as `just cli <subcommand>` (an alias for `dune exec bin/main.exe -- <subcommand>`):

- `mml2rw <file>` -- compile a MiniML module to RichWasm
- `ll2rw <file>` -- compile a LinLang module to RichWasm
- `rw-elab <file>` -- elaborate a RichWasm module (sexp) with full type annotations
- `rw2wasm <file>` -- typecheck a RichWasm module (sexp) and compile it to WebAssembly (wat)
- `run <file>` -- like `rw2wasm`, then assemble with `wat2wasm` and execute on the runtime

Every subcommand reads the given file, or stdin if the argument is `-` or omitted. `mml2rw`, `ll2rw`, and `rw-elab` accept `-pp {pp|sexp|rocq}` to select the output format and `-elab {true|false}` (default `true`) to toggle elaboration of the output.

- `run-dir <dir>` -- compile every `.mml`, `.ll`, `.rw` (sexp), and `.wat` file in `dir`, link them as `dir/links.sexp` says, and run the one exporting `_start`

A module is named after its file without the extension, and each entry of `links.sexp`, `((importer m) (index i) (provider p) (export e))`, fills import `i` of module `m` with export `e` of module `p`.

`rw2wasm`, `run`, and `run-dir` use the typechecker and compiler extracted from the Rocq development.

For example:

```sh
# pretty-print the compiled RichWasm
$ just cli ll2rw tests/examples/standalone/safe_div.ll
# run the safe_div with the RichWasm runtime
$ just cli run tests/examples/standalone/safe_div.rw
0
```

(`safe_div.rw` is `ll2rw -pp sexp -elab false` applied to `safe_div.ll`; dividing by zero takes the error branch, which the caller maps to `0`.)

### Running the examples

```sh
$ just cli run-dir examples/05-add3-ll-calls-ml
7
```

Each example's `expected` file holds its output, and `dune test` checks them all. `11-precompiled` is assembled by dune, so run `_build/default/examples/11-precompiled` instead.

### Web demo

The web demo runs these examples in the browser. For each module it shows the RichWasm, the elaborated RichWasm, and the Wasm that its source compiles to. The Run button links the modules and prints the program's output next to `expected`. You can edit any file or add new ones.

`web/build.sh` builds the demo into `web/dist` from `nix develop` or the Docker image. It fetches its JavaScript dependencies with npm, so it needs network access. Serve `web/dist` over HTTP, for example with `python3 -m http.server -d web/dist`, and open http://localhost:8000. From a `file://` page, Chrome won't start the demo's workers. The demo needs Chrome 120+ or Firefox 125+ for WebAssembly multi-memory. At the time of writing, the latest Safari doesn't have it, though Safari Technology Preview 250+ does.

## Differences between paper and mechanization
- Kinds are baked into the type syntax to allow the compiler access to them. These kinds are defined to be the most specific kinds, with subkinding allowed only in specific locations. Instruction types are also baked into instruction syntax.
- Function types: in the paper, a function type is `forall a*.xi`, where a* can be a list of quantifiers in any order. The mechanized syntax differs by ensuring that all `t:kappa` quantifiers are inner-most by stratifying functions types into `function_type` and `inner_function_type`. This was done to simplify flatenning and indexing (as type quantifiers can rely on previously declared variables).
- The live memory resource is named the "runtime token" and is appreviated `RT`.
- The `dup` instruction in the paper is `copy` in the mechanization.

## Important Files
This overview will focus on the most important files and folders, as it relates to the paper. 

### Language and Compiler.
`theories/syntax/rw.sig`: RichWasm syntax, using autosubst.

`theories/typing.v`: the type system.

`theories/typechecker/typechecker.v`: typechecker.

`theories/compiler`: the RichWasm to Wasm compiler.

### Model
`theories/iris/logrel.v`: the main logical relation. `type_interp` and `closure_interp` for type and closure interpretation. `have_instr_type_sem` for instruction logical relation. `module_interp` for the module interpretation.

`theories/iris/memory.v`: memory model. `rt_token` for the run time token.

`theories/iris/runtime.v`: runtime specifications

`theories/iris/language/cwp/def.v`: definition of the new weakest precondition modality, CWP.

### FTLR
`theories/iris/logrel/instr/typing.v`: statement of Theorem 5.1

`theories/iris/logrel/instr/typing folder`: proofs of ABI compliance for each RichWasm instruction, supported by helper files in the `theories/iris/logrel/instr` folder.

### Examples
`src` contains our case study compilers, and `tests` test case study + RichWasm compilers all together. `tests/e2e/main.ml` has the glue code and linking type examples.

`theories/examples`: the two proofs of linking with external Wasm.

### Axioms

We rely on the following additional
axioms. `ClassicalDedekindReals.sig_not_dec`,
`ClassicalDedekindReals.sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Classical_Prop.classic` are used by the definition of floating-point Wasm
numbers, which we inherit from Iris-Wasm.

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec :
  ∀ P : nat → Prop,
    (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
FunctionalExtensionality.functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```
