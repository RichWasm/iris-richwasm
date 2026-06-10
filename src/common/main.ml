open! Base
open! Stdlib.Format

let elaborate = Elaborate.elab_module

let compile modul =
  let open Richwasm_extract.Module0 in
  match compile_module modul with
  | Coq_inl err -> Error err
  | Coq_inr modul -> Ok modul

let wasm_serialize = Richwasm_extract.Binary_format_printer.binary_of_module
let wasm_ugly_printer = Wasm_ugly_printer.ugly_module

let typecheck modul =
  let open Richwasm_extract.Typechecker in
  match has_module_type_checker_with_synth modul with
  | Coq_inl () -> Ok ()
  | Coq_inr err -> Error err
