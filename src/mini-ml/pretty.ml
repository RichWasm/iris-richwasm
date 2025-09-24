open! Core
open Format
open Syntax

let rec pp_pretype ff pt =
  let open Source.PreType in
  match pt with
  | Int -> fprintf ff "int"
  | Var v -> fprintf ff "'%s" v
  | Ref t -> fprintf ff "@[(ref@ %a)@]" pp_type t
  | Prod ts -> fprintf ff "@[<hov 2>(*@ %a)@]" (pp_print_list pp_type) ts
  | Sum ts -> fprintf ff "@[<hov 2>(+@ %a)@]" (pp_print_list pp_type) ts
  | Rec (v, t) -> fprintf ff "@[<hov 2>(rec@ %s@ %a)]" v pp_type t
  | Fun {foralls; arg; ret} ->
      fprintf ff "@[<hov 2>(->@ [%a]@ %a@ %a)]"
        (pp_print_list pp_print_string)
        foralls pp_type arg pp_type ret

and pp_type ff (t : Source.Type.t) = pp_pretype ff t

let pp_op ff op =
  op
  |> (function
       | `Add -> "+"
       | `Sub -> "-"
       | `Mul -> "*"
       | `Div -> "/" )
  |> pp_print_string ff
;;

let rec pp_value ff v =
  let open Source.Value in
  match v with
  | Int i -> fprintf ff "%i" i
  | Var v -> fprintf ff "%s" v
  | Tuple vs -> fprintf ff "@[<hov 2>(tuple@ %a)@]" (pp_print_list pp_value) vs
  | Inj (case, v, t) ->
      fprintf ff "@[<hov 2>(inj@ %i@ %a@ %a)@]" case pp_value v pp_type t
  | Fun {foralls; arg; ret_type; body} ->
      fprintf ff "@[<hov 2>(λ@ [%a]@ @[<hov 2>(:@ (%a)@ %a)@]@,@[<v 2>%a@])]"
        (pp_print_list pp_print_string)
        foralls
        (pp_print_list (fun ff (v, t) -> fprintf ff "[:@ %s@ %a]" v pp_type t))
        [arg] pp_type ret_type pp_expr body

and pp_expr ff e =
  let open Source.Expr in
  match e with
  | Value v -> fprintf ff "%a" pp_value v
  | Apply (f, ts, arg) ->
      fprintf ff "@[<hov 2>(%a@ [%a]@ %a)@]" pp_value f (pp_print_list pp_type)
        ts pp_value arg
  | Project (pos, v) -> fprintf ff "@[<hov 2>(π@ %i@ %a)@]" pos pp_value v
  | Op (op, l, r) ->
      fprintf ff "@[<hov 2>(%a@ %a@ %a)@]" pp_op op pp_value l pp_value r
  | If0 (c, thn, els) ->
      fprintf ff "@[<hov 2>(if0@ %a@,@[<v 2>%a@]@,@[<v 2>%a@])@]" pp_value c
        pp_expr thn pp_expr els
  | Cases (v, branches) ->
      fprintf ff "@[<hov 2>(cases@ %a%a)@]" pp_value v
        (pp_print_list (fun ff ((v, t), e) ->
             fprintf ff "@,@[<v 2>[@[<hov 2>(:@ %s@ %a)@]@ %a]@]" v pp_type t
               pp_expr e ) )
        branches
  | New v -> fprintf ff "@[<hov 2>(new@ %a)@]" pp_value v
  | Deref v -> fprintf ff "@[<hov 2>(!@ %a)@]" pp_value v
  | Assign (r, v) -> fprintf ff "@[<hov 2>(:=@ %a@  %a)@]" pp_value r pp_value v
  | Let ((name, ty), v, body) ->
      fprintf ff "@[<hov 2>(let@ @[<hov 2>([:@ %s@ %a]@ %a)@]@,@[<v 2>%a@])@]"
        name pp_type ty pp_expr v pp_expr body
  | Fold (t, v) -> fprintf ff "@[<hov 2>(fold@ [%a]@ %a)@]" pp_type t pp_value v
  | Unfold v -> fprintf ff "@[<hov 2>(unfold@ %a)@]" pp_value v
;;

let pp_import ff (Source.Module.Import (v, t)) =
  fprintf ff "@[<hov 2>(import@ %s@ %a)@]" v pp_type t
;;

let pp_item ff item =
  let open Source.Module in
  let kw, v, t, e =
    match item with
    | Private ((v, t), e) -> ("fn", v, t, e)
    | Export ((v, t), e) -> ("export", v, t, e)
  in
  fprintf ff "@[<hov 2>(%s@ %s@ [%a]@,@[<v 2>%a@])@]" kw v pp_type t pp_expr e
;;

let pp_module ff (Source.Module.Module (imps, items, maybe_main)) =
  let body ff maybe_main =
    match maybe_main with
    | None -> pp_print_string ff ""
    | Some e -> pp_expr ff e
  in
  fprintf ff "@[<hov 2>(%a@,%a@,%a)@]" (pp_print_list pp_import) imps
    (pp_print_list pp_item) items body maybe_main
;;
