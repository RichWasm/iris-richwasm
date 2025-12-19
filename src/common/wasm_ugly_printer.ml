open! Base
open! Stdlib.Format
open Monads
module Ast = Richwasm_extract.Datatypes0
open Util

module State = struct
  type t = { output : string }

  let init ?(output = "") () : t = { output }
end

module Void = struct
  type t = |
end

module M = struct
  module Inner = StateM (State) (Void)
  include Inner

  type t = unit Inner.t

  let[@warning "-23"] append (str : String.t) : t =
    modify (fun s -> { s with output = s.output ^ str })

  let appendf fmt = kasprintf (fun s -> append s) fmt
end

open M

let pp_limits ff ({ lim_min; lim_max } : Ast.limits) =
  fprintf ff "%a" Z.pp_print lim_min;
  match lim_max with
  | Some x -> fprintf ff " %a" Z.pp_print x
  | None -> ()

let ugly_table ({ tt_limits; tt_elem_type = ELT_funcref } : Ast.module_table) :
    t =
  appendf "(table %a funcref)" pp_limits tt_limits

let ugly_mem lim : t = appendf "(memory %a)" pp_limits lim

let pp_value_type ff : Ast.value_type -> unit = function
  | T_i32 -> fprintf ff "i32"
  | T_i64 -> fprintf ff "i64"
  | T_f32 -> fprintf ff "f32"
  | T_f64 -> fprintf ff "f64"

let ugly_global_type ({ tg_mut; tg_t } : Ast.global_type) : t =
  let* () = append "(" in
  let* () =
    match tg_mut with
    | MUT_immut -> ret ()
    | MUT_mut -> append "mut "
  in
  let* () = appendf "%a" pp_value_type tg_t in
  let* () = append ")" in
  ret ()

(* NOTE: if updating to newer wasm spec, likely won't be able to reuse ugly_{table,mem} anymore *)
let ugly_import_desc : Ast.import_desc -> t = function
  | ID_func type_idx -> appendf "(func (type %a))" Z.pp_print type_idx
  | ID_table table_typ -> ugly_table table_typ
  | ID_mem lim -> ugly_mem lim
  | ID_global glob_typ ->
      let* () = append "(global " in
      let* () = ugly_global_type glob_typ in
      append ")"

let pp_name ff (name : Ast.name) =
  fprintf ff "%a" String.pp (String.of_char_list name)

let ugly_import ({ imp_module; imp_name; imp_desc } : Ast.module_import) : t =
  let* () = appendf "(import %a %a" pp_name imp_module pp_name imp_name in
  let* () = ugly_import_desc imp_desc in
  let* () = append ")" in
  ret ()

let pp_print_hard_space ff () = fprintf ff " "
let pp_print_nothing ff () = fprintf ff ""

let rec ugly_instruction (instr : Ast.basic_instruction) : t =
  let pp_sx ff : Ast.sx -> unit = function
    | SX_U -> fprintf ff "u"
    | SX_S -> fprintf ff "s"
  in
  let vt_is_int : Ast.value_type -> bool = function
    | T_i32 | T_i64 -> true
    | T_f32 | T_f64 -> false
  in
  let vt_is_float : Ast.value_type -> bool = function
    | T_i32 | T_i64 -> false
    | T_f32 | T_f64 -> true
  in
  let handle_bt : Ast.function_type -> t = function
    | Tf (param, result) ->
        let* () =
          appendf "(param%a)" (pp_print_list_pre_space pp_value_type) param
        in
        let* () =
          appendf "(result%a)" (pp_print_list_pre_space pp_value_type) result
        in
        ret ()
  in

  match instr with
  | BI_unreachable -> append "unreachable"
  | BI_nop -> append "nop"
  | BI_drop -> append "drop"
  | BI_select -> append "select"
  | BI_return -> append "return"
  | BI_block (bt, body) ->
      let* () = append "block" in
      let* () = handle_bt bt in
      let* () = ugly_expr body in
      append " end"
  | BI_loop (bt, body) ->
      let* () = append "loop" in
      let* () = handle_bt bt in
      let* () = ugly_expr body in
      append " end"
  | BI_if (bt, thn, els) ->
      let* () = append "if" in
      let* () = handle_bt bt in
      let* () = ugly_expr thn in
      let* () = append " else" in
      let* () = ugly_expr els in
      append " end"
  | BI_br label -> appendf "br %a" Z.pp_print label
  | BI_br_if label -> appendf "br_if %a" Z.pp_print label
  | BI_br_table (labels, default_label) ->
      appendf "br_table %a %a"
        (pp_print_list ~pp_sep:pp_print_hard_space Z.pp_print)
        labels Z.pp_print default_label
  | BI_call func_idx -> appendf "call %a" Z.pp_print func_idx
  | BI_call_indirect type_idx ->
      appendf "call_indirect (type %a)" Z.pp_print type_idx
  | BI_get_local local_idx -> appendf "local.get %a" Z.pp_print local_idx
  | BI_set_local local_idx -> appendf "local.set %a" Z.pp_print local_idx
  | BI_tee_local local_idx -> appendf "local.tee %a" Z.pp_print local_idx
  | BI_get_global global_idx -> appendf "global.get %a" Z.pp_print global_idx
  | BI_set_global global_idx -> appendf "global.set %a" Z.pp_print global_idx
  | BI_load (mem_idx, vt, _, align, offset) ->
      appendf "%a.load %a offset=%a align=%a" pp_value_type vt Z.pp_print
        mem_idx Z.pp_print offset Z.pp_print align
  | BI_store (mem_idx, vt, _, align, offset) ->
      appendf "%a.store %a offset=%a align=%a" pp_value_type vt Z.pp_print
        mem_idx Z.pp_print offset Z.pp_print align
  | BI_current_memory mem_idx -> appendf "memory.size %a" Z.pp_print mem_idx
  | BI_grow_memory mem_idx -> appendf "memory.grow %a" Z.pp_print mem_idx
  | BI_const v ->
      let append_const (kind : string) (z : Z.t) : M.t =
        appendf "%s.const %s" kind (Z.to_string z)
      in
      (* 😬 *)
      let obj_magic = Stdlib.Obj.magic in
      let module Wasm_int = Richwasm_extract.Numerics.Wasm_int in
      let module Wasm_float = Richwasm_extract.Numerics.Wasm_float in
      let module IntZ = Richwasm_extract.Integers.Int in
      (match v with
      | VAL_int32 v ->
          append_const "i32" (Wasm_int.Int32.unsigned (obj_magic v))
      | VAL_int64 v ->
          append_const "i64" (Wasm_int.Int64.unsigned (obj_magic v))
      | VAL_float32 v ->
          append_const "f32"
            (IntZ.unsigned (Wasm_float.FloatSize32.to_bits (obj_magic v)))
      | VAL_float64 v ->
          append_const "f64"
            (IntZ.unsigned (Wasm_float.FloatSize64.to_bits (obj_magic v))))
  | BI_unop (vt, unop) ->
      let* () = appendf "%a." pp_value_type vt in
      (match unop with
      | Unop_i UOI_clz -> append "clz"
      | Unop_i UOI_ctz -> append "ctz"
      | Unop_i UOI_popcnt -> append "popcnt"
      | Unop_f UOF_neg -> append "neg"
      | Unop_f UOF_abs -> append "abs"
      | Unop_f UOF_ceil -> append "ceil"
      | Unop_f UOF_floor -> append "floor"
      | Unop_f UOF_trunc -> append "trunc"
      | Unop_f UOF_nearest -> append "nearest"
      | Unop_f UOF_sqrt -> append "sqrt")
  | BI_binop (vt, binop) ->
      let* () = appendf "%a." pp_value_type vt in
      (match binop with
      | Binop_i BOI_add -> append "add"
      | Binop_i BOI_sub -> append "sub"
      | Binop_i BOI_mul -> append "mul"
      | Binop_i (BOI_div sx) -> appendf "div_%a" pp_sx sx
      | Binop_i (BOI_rem sx) -> appendf "rem_%a" pp_sx sx
      | Binop_i BOI_and -> append "and"
      | Binop_i BOI_or -> append "or"
      | Binop_i BOI_xor -> append "xor"
      | Binop_i BOI_shl -> append "shl"
      | Binop_i (BOI_shr sx) -> appendf "shr_%a" pp_sx sx
      | Binop_i BOI_rotl -> append "rotl"
      | Binop_i BOI_rotr -> append "rotr"
      | Binop_f BOF_add -> append "add"
      | Binop_f BOF_sub -> append "sub"
      | Binop_f BOF_mul -> append "mul"
      | Binop_f BOF_div -> append "div"
      | Binop_f BOF_min -> append "min"
      | Binop_f BOF_max -> append "max"
      | Binop_f BOF_copysign -> append "copysign")
  | BI_testop (vt, testop) ->
      let* () = appendf "%a." pp_value_type vt in
      (match testop with
      | TO_eqz -> append "eqz")
  | BI_relop (vt, relop) ->
      let* () = appendf "%a." pp_value_type vt in
      (match relop with
      | Relop_i ROI_eq -> append "eq"
      | Relop_i ROI_ne -> append "ne"
      | Relop_i (ROI_lt sx) -> appendf "lt_%a" pp_sx sx
      | Relop_i (ROI_gt sx) -> appendf "gt_%a" pp_sx sx
      | Relop_i (ROI_le sx) -> appendf "le_%a" pp_sx sx
      | Relop_i (ROI_ge sx) -> appendf "ge_%a" pp_sx sx
      | Relop_f ROF_eq -> append "eq"
      | Relop_f ROF_ne -> append "ne"
      | Relop_f ROF_lt -> append "lt"
      | Relop_f ROF_gt -> append "gt"
      | Relop_f ROF_le -> append "le"
      | Relop_f ROF_ge -> append "ge")
  | BI_cvtop (T_i32, CVO_convert, T_i64, None) -> append "i32.wrap_i64"
  | BI_cvtop (T_i64, CVO_convert, T_i32, Some sx) ->
      appendf "i64.extend_i32_%a" pp_sx sx
  | BI_cvtop (vt1, CVO_convert, vt2, Some sx)
    when vt_is_int vt1 && vt_is_float vt2 ->
      appendf "%a.trunc_%a_%a" pp_value_type vt1 pp_value_type vt2 pp_sx sx
  | BI_cvtop (T_f32, CVO_convert, T_f64, None) -> append "f32.demote_f64"
  | BI_cvtop (T_f64, CVO_convert, T_f32, None) -> append "f64.promote_f32"
  | BI_cvtop (vt1, CVO_convert, vt2, Some sx)
    when vt_is_float vt1 && vt_is_int vt2 ->
      appendf "%a.convert_%a_%a" pp_value_type vt1 pp_value_type vt2 pp_sx sx
  | BI_cvtop (vt1, CVO_reinterpret, vt2, None) ->
      appendf "%a.reinterpret_%a" pp_value_type vt1 pp_value_type vt2
  | BI_cvtop _ -> failwith "invalid cvtop"

and ugly_expr (expr : Ast.basic_instruction list) : t =
  iterM ~f:(fun x -> append " " >>= fun _ -> ugly_instruction x) expr

let ugly_func ({ modfunc_type; modfunc_locals; modfunc_body } : Ast.module_func)
    : t =
  let* () =
    appendf "(func (type %a) (local %a)" Z.pp_print modfunc_type
      (pp_print_list ~pp_sep:pp_print_hard_space pp_value_type)
      modfunc_locals
  in
  let* () = ugly_expr modfunc_body in
  append ")"

let ugly_global ({ modglob_type; modglob_init } : Ast.module_glob) : t =
  let* () = append "(global " in
  let* () = ugly_global_type modglob_type in
  let* () = ugly_expr modglob_init in
  append ")"

let ugly_elem
    ({ modelem_table; modelem_offset; modelem_init } : Ast.module_element) : t =
  let* () = appendf "(elem %a (offset" Z.pp_print modelem_table in
  let* () = ugly_expr modelem_offset in
  let* () = append ")" in
  let* () =
    appendf "%a"
      (pp_print_list ~pp_sep:pp_print_hard_space Z.pp_print)
      modelem_init
  in
  append ")"

(* NOTE: the AST should probably support multiple memories, but isn't needed for RichWasm *)
let ugly_data ({ moddata_data; moddata_offset; moddata_init } : Ast.module_data)
    : t =
  let* () = appendf "(data %a (offset" Z.pp_print moddata_data in
  let* () = ugly_expr moddata_offset in
  appendf ") %a)" String.pp (String.of_char_list moddata_init)

let ugly_export_desc : Ast.module_export_desc -> t = function
  | MED_func func_idx -> appendf "(func %a)" Z.pp_print func_idx
  | MED_table table_idx -> appendf "(table %a)" Z.pp_print table_idx
  | MED_mem mem_idx -> appendf "(memory %a)" Z.pp_print mem_idx
  | MED_global global_idx -> appendf "(global %a)" Z.pp_print global_idx

let ugly_export ({ modexp_name; modexp_desc } : Ast.module_export) : t =
  let* () = appendf "(export %a " pp_name modexp_name in
  let* () = ugly_export_desc modexp_desc in
  append ")"

(* NOTE: this function must not `emit` *)
let ugly_type (Tf (t_in, t_out) : Ast.function_type) : t =
  let vt_lst = pp_print_list ~pp_sep:pp_print_hard_space pp_value_type in
  appendf "(type (func (param %a) (result %a)))" vt_lst t_in vt_lst t_out

let ugly_module
    ({
       mod_types;
       mod_funcs;
       mod_tables;
       mod_mems;
       mod_globals;
       mod_elem;
       mod_data;
       mod_start;
       mod_imports;
       mod_exports;
     } :
      Ast.coq_module) =
  let m =
    let* () = append "(module " in
    (* NOTE: imports must go first *)
    let* () = iterM ~f:ugly_import mod_imports in
    let* () = iterM ~f:ugly_func mod_funcs in
    let* () = iterM ~f:ugly_table mod_tables in
    let* () = iterM ~f:ugly_mem mod_mems in
    let* () = iterM ~f:ugly_global mod_globals in
    let* () = iterM ~f:ugly_elem mod_elem in
    let* () = iterM ~f:ugly_data mod_data in
    let* () =
      match mod_start with
      | Some idx -> appendf "(start %a)" Z.pp_print idx
      | None -> ret ()
    in
    let* () = iterM ~f:ugly_export mod_exports in

    let* () = iterM ~f:ugly_type mod_types in

    let* () = append ")" in
    ret ()
  in
  let init_st = State.init () in
  match m init_st with
  | Ok ((), st) -> st.output
  | _ -> .
