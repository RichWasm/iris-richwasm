open Sexplib.Std
open Format

module Types = struct
  type variable = string
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type typ = Int | Lolipop of typ * typ | Prod of typ * typ | Ref of typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binding = variable * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of variable
    | Int of int
    | Lam of binding * typ * expr
    | Prod of value * value
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  and expr =
    | Val of value
    | App of value * value
    | Let of binding * expr * expr
    | If0 of value * expr * expr
    | Binop of [ `Add | `Sub | `Mul | `Div ] * value * value
    | LetPair of binding * binding * expr * expr
    | New of value
    | Swap of value * value
    | Free of value
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type import = Import of typ * variable
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type toplevel = TopLevel of bool * binding * expr (* export *)
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type modul = Module of import list * toplevel list * expr option
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]
end

module Printers = struct
  (* open Types *)

  let pp_var ff x = fprintf ff "%s" x

  let rec pp_typ ff (t : Types.typ) =
    match t with
    | Int -> fprintf ff "int"
    | Lolipop (t1, t2) ->
        fprintf ff "@[<hov 2>(%a@ ⊸@ %a)@]" pp_typ t1 pp_typ t2
    | Prod (t1, t2) -> fprintf ff "@[<hov 2>(%a@ ⊗@ %a)@]" pp_typ t1 pp_typ t2
    | Ref t -> fprintf ff "@[<hov 2>(ref@ %a)@]" pp_typ t

  let pp_binding ff ((x, t) : Types.binding) =
    Format.fprintf ff "(@[<hov 1>%a@ :@ %a@])" pp_var x pp_typ t

  let pp_binop ff = function
    | `Add -> fprintf ff "+"
    | `Sub -> fprintf ff "-"
    | `Mul -> fprintf ff "×"
    | `Div -> fprintf ff "÷"

  let rec pp_val ff (v : Types.value) =
    match v with
    | Var x -> pp_var ff x
    | Int n -> fprintf ff "%d" n
    | Lam (bind, ret, body) ->
        fprintf ff "@[<hov 2>(λ@ %a@ :@ %a@ .@\n@[<v 2>%a@])@]" pp_binding bind
          pp_typ ret pp_expr body
    | Prod (l, r) -> fprintf ff "@[<hov 2>(%a,@ %a)@]" pp_val l pp_val r

  and pp_expr ff (e : Types.expr) =
    match e with
    | Val v -> pp_val ff v
    | App (l, r) -> fprintf ff "@[<hov 2>(app@ %a@ %a)@]" pp_val l pp_val r
    | Let (bind, e, body) ->
        fprintf ff "@[<hv 0>let@ %a@ =@ @[<hv 2>%a@]@ in@ @[<hv 0>%a@]@]"
          pp_binding bind pp_expr e pp_expr body
    | If0 (v, e1, e2) ->
        fprintf ff "@[<hv 0>if0@ %a@ then@,@[<hv 2>%a@]@,else@,@[<hv 2>%a@]@]"
          pp_val v pp_expr e1 pp_expr e2
    | Binop (op, l, r) ->
        fprintf ff "@[<hov 2>(%a@ %a@ %a)@]" pp_val l pp_binop op pp_val r
    | LetPair (b1, b2, e, b) ->
        fprintf ff "@[<hv 0>let@ (%a,@ %a)@ =@ @[<hv 2>%a@]@ in@ @[<hv 0>%a@]@]"
          pp_binding b1 pp_binding b2 pp_expr e pp_expr b
    | New v -> fprintf ff "@[<hov 2>(new@ %a)@]" pp_val v
    | Swap (l, r) -> fprintf ff "@[<hov 2>(swap@ %a@ %a)@]" pp_val l pp_val r
    | Free v -> fprintf ff "@[<hov 2>(free@ %a)@]" pp_val v

  let pp_import ff (Types.Import (t, x)) =
    fprintf ff "@[<hov 2>(import@ %a@ :@ %a)@]" pp_var x pp_typ t

  let pp_toplevel ff (Types.TopLevel (export, b, e)) =
    let export_str = if export then "export " else "" in
    fprintf ff "@[<hov 2>%slet@ %a@ =@ @[<hv 2>%a@]@]" export_str pp_binding b
      pp_expr e

  let pp_modul ff (Types.Module (imports, toplevels, main_expr)) =
    let pp_list pp ff xs =
      List.iteri
        (fun i x ->
          if i > 0 then fprintf ff "@;";
          pp ff x)
        xs
    in
    fprintf ff "@[<v 0>";
    if imports <> [] then (
      pp_list pp_import ff imports;
      fprintf ff "@,@,");
    if toplevels <> [] then (
      pp_list pp_toplevel ff toplevels;
      fprintf ff "@,@,");
    Option.iter (fun e -> fprintf ff "%a" pp_expr e) main_expr;
    fprintf ff "@]"

  let string_of_var x = asprintf "%a" pp_var x
  let string_of_typ t = asprintf "%a" pp_typ t
  let string_of_val v = asprintf "%a" pp_val v
  let string_of_expr e = asprintf "%a" pp_expr e
  let string_of_modul m = asprintf "%a" pp_modul m
end

module Var = struct
  type t = Types.variable [@@deriving show, eq, iter, map, fold, sexp]

  let pp = Printers.pp_var
  let string_of = Printers.string_of_var
end

module Val = struct
  type t = Types.value [@@deriving show, eq, iter, map, fold, sexp]

  let pp = Printers.pp_val
  let string_of = Printers.string_of_val
end

module Expr = struct
  type t = Types.expr [@@deriving show, eq, iter, map, fold, sexp]

  let pp = Printers.pp_expr
  let string_of = Printers.string_of_expr
end

module Type = struct
  type t = Types.typ [@@deriving show, eq, iter, map, fold, sexp]

  let pp = Printers.pp_typ
  let string_of = Printers.string_of_typ
end

module Module = struct
  type t = Types.modul [@@deriving show, eq, iter, map, fold, sexp]

  let pp = Printers.pp_modul
  let string_of = Printers.string_of_modul
end
