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

let rec pp_typecheck_error ff =
  let open Annotated_syntax in
  let open Richwasm_extract.Typechecker in
  function
  | NormalError s -> fprintf ff "%s" s
  | FrameError (s, a, b) ->
      let pp_it = InstructionType.pp in
      fprintf ff
        "@[<v 2>Frame error: %s@,@[<2>1st instr: %a@]@,@[<2>2nd instr: %a@]@]" s
        pp_it a pp_it b
  | LocalCtxSynthError (s, l, l', errs) ->
      let pp_lctx = pp_rocq_list Type.pp in
      fprintf ff
        "@[<v 2>Local ctx synth error: %s @,\
         @[<2>initial lctx: %a@]@,\
         @[<2>synthed lctx: %a@]@,\
         %a@]"
        s pp_lctx l pp_lctx l' pp_typecheck_errors errs
  | HasKindError (s, errs) ->
      fprintf ff "@[<v 2>Has kind error: %s @,%a@]" s pp_typecheck_errors errs

and pp_typecheck_errors ff =
  let pp_list = pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@;") in
  fprintf ff "@[<2>%a@]" (pp_list pp_typecheck_error)

(** Serialize [_start]'s result types (sexp) for the host walker; [None] if no
    [_start]. *)
let start_type_sexp (m : Syntax.Module.t) : string option =
  let open Syntax in
  let num_imports = List.length m.Module.imports in
  List.find_map m.Module.exports ~f:(fun (e : Module.Export.t) ->
      match e.Module.Export.desc with
      | Module.Export.Desc.Func idx
        when String.equal e.Module.Export.name "_start" ->
          List.nth m.Module.functions (idx - num_imports)
          |> Option.map ~f:(fun (f : Module.Function.t) ->
              let (FunctionType.FunctionType (_, _, results)) =
                f.Module.Function.typ
              in
              Sexp.to_string ([%sexp_of: Type.t list] results))
      | _ -> None)
