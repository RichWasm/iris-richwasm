open! Base
open Stdlib.Format
module MiniMlSyntax = Syntax
module RichWasmSyntax = Richwasm_common.Syntax

module CompileErr = struct
  type t =
    | Parse of Parse.Err.t
    | Convert of Convert.Err.t
    | Codegen of Codegen.Err.t
  [@@deriving sexp_of, variants]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Richwasm_common.Monads.LogResultM (CompileErr) (String)

type compile_res = RichWasmSyntax.Module.t Res.t

(* need rank2 polymorphism *)
type asprintf = { asprintf : 'a. ('a, formatter, unit, string) format4 -> 'a }

let ( >>? ) ~(asprintf : asprintf) m (name, f, pp, err_map) =
  let open Res in
  let log_pp x : unit t =
    let len = String.length name in
    let fill = '=' in
    tell
      (asprintf.asprintf "@{<blue>%a@} @{<orange>%s@} @{<blue>%a@}@.%a"
         (Richwasm_common.Util.pp_pad ~fill ~len)
         false name
         (Richwasm_common.Util.pp_pad ~fill ~len)
         true pp x)
  in

  m >>= fun x ->
  f x |> Result.map_error ~f:err_map |> lift_result >>= fun y ->
  log_pp y >>= fun () -> ret y

let pp_closed_module ff m =
  Sexp.pp_hum ff (MiniMlSyntax.Closed.Module.sexp_of_t m)

let compile_ast
    ?(asprintf : asprintf = { asprintf })
    (ast : MiniMlSyntax.Source.Module.t) : compile_res =
  let open CompileErr in
  let module RWMod = RichWasmSyntax.Module in
  let ( >>? ) x y = ( >>? ) ~asprintf x y in
  Res.ret ast
  >>? ("convert", Convert.cc_module, pp_closed_module, convert)
  >>? ("codegen", Codegen.compile_module, RWMod.pp, codegen)

let compile_str ?(asprintf : asprintf = { asprintf }) (str : string) :
    compile_res =
  let open Res in
  let ( >>? ) x y = ( >>? ) ~asprintf x y in
  ret str
  >>? ("parse", Parse.from_string, Pretty.pp_module, CompileErr.parse)
  >>= compile_ast ~asprintf
