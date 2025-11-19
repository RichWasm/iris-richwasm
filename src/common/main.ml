open! Base
open! Stdlib.Format

let elaborate = Elaborate.elab_module

let pp_compile_err ff : Richwasm_extract.Prelude.error -> unit = function
  | ETodo -> fprintf ff "ETodo"
  | EFail -> fprintf ff "EFail"

let compile modul =
  let open Richwasm_extract.Module0 in
  let compiled = compile_module modul in
  let compiled' = run_modgen compiled in
  match compiled' mod_empty with
  | Coq_inl err -> Error err
  | Coq_inr (_, modul) -> Ok modul

let wasm_serialize = Richwasm_extract.Binary_format_printer.binary_of_module
let wasm_ugly_printer = Wasm_ugly_printer.ugly_module
