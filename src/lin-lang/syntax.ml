open! Base
open Stdlib.Format
open Util

module Variable = struct
  type t = string [@@deriving eq, ord, sexp]

  let pp ff = fprintf ff "@[%s@]"
  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Type = struct
  type t =
    | Int
    | Var of Variable.t
    | Lollipop of t * t
    | Prod of t list
    | Sum of t list
    | Rec of Variable.t * t
    | Ref of t
  [@@deriving eq, ord, variants, sexp]

  let rec pp ff : t -> unit = function
    | Int -> fprintf ff "@[int@]"
    | Var x -> fprintf ff "@[%a@]" Variable.pp x
    | Lollipop (t1, t2) -> fprintf ff "@[(%a@ ⊸@ %a)@]" pp t1 pp t2
    | Prod ts -> pp_sep pp ff ~sep:"⊗" ts
    | Sum ts -> pp_sep pp ff ~sep:"⊕" ts
    | Rec (x, t) -> fprintf ff "@[(rec %a %a)@]" Variable.pp x pp t
    | Ref t -> fprintf ff "@[(ref@ %a)@]" pp t

  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Binding = struct
  type t = Variable.t * Type.t [@@deriving eq, ord, sexp]

  let pp ff ((x, t) : t) = fprintf ff "@[(%a@ :@ %a)@]" Variable.pp x Type.pp t
  let string_of = asprintf "%a" pp
end

module Binop = struct
  type t =
    | Add
    | Sub
    | Mul
    | Div
  [@@deriving eq, ord, variants, sexp]

  let pp ff : t -> unit = function
    | Add -> fprintf ff "+"
    | Sub -> fprintf ff "-"
    | Mul -> fprintf ff "×"
    | Div -> fprintf ff "÷"

  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Expr = struct
  type t =
    | Var of Variable.t
    | Int of int
    | Lam of Binding.t * Type.t * t
    | Tuple of t list
    | Inj of int * t * Type.t
    | Fold of Type.t * t
    | App of t * t
    | Let of Binding.t * t * t
    | Split of Binding.t list * t * t
    | Cases of t * (Binding.t * t) list
    | Unfold of Type.t * t
    | If0 of t * t * t
    | Binop of Binop.t * t * t
    | New of t
    | Swap of t * t
    | Free of t
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff (e : t) =
    match e with
    | Var x -> Variable.pp ff x
    | Int n -> fprintf ff "%d" n
    | Lam (bind, ret, body) ->
        fprintf ff "@[<v 2>@[<2>(λ@ %a@ :@ %a@ @].@;@[<2>%a@])@]" Binding.pp
          bind Type.pp ret pp body
    | Tuple es ->
        fprintf ff "@[<2>(";
        pp_list (fun x -> fprintf ff "%a" pp x) (fun () -> fprintf ff ",@ ") es;
        fprintf ff ")@]"
    | Inj (i, e, t) ->
        fprintf ff "@[<2>(inj %a@ %a@ :@ %a)@]" Int.pp i pp e Type.pp t
    | Fold (t, e) -> fprintf ff "@[<2>(fold %a@ %a)@]" Type.pp t pp e
    | App (l, r) -> fprintf ff "@[<2>(app@ %a@ %a)@]" pp l pp r
    | Let (bind, e, body) ->
        fprintf ff "@[<v 0>@[<2>(let@ %a@ =@ %a@ in@]@;@[<2>%a)@]@]" Binding.pp
          bind pp e pp body
    | Split (bs, e, b) ->
        fprintf ff "@[<v 0>@[<2>(split@ ";
        pp_list
          (fun x -> fprintf ff "%a" Binding.pp x)
          (fun () -> fprintf ff "@ ")
          bs;
        fprintf ff "@ =@ %a@ in@]@;@[<2>%a)@]@]" pp e pp b
    | Cases (scrutinee, cases) ->
        fprintf ff "@[<v 2>@[<2>(cases %a@]@;" pp scrutinee;
        pp_list
          (fun (binding, body) ->
            fprintf ff "@[<2>(case %a@ %a)@]" Binding.pp binding pp body)
          (fun () -> fprintf ff "@;")
          cases;
        fprintf ff "@[<2>)@]@]"
    | Unfold (t, e) -> fprintf ff "@[(unfold %a %a)@]" Type.pp t pp e
    | If0 (e1, e2, e3) ->
        fprintf ff "@[<2>(if0 %a@;then %a@;else@ %a)@]" pp e1 pp e2 pp e3
    | Binop (op, l, r) -> fprintf ff "@[<2>(%a@ %a@ %a)@]" pp l Binop.pp op pp r
    | New e -> fprintf ff "@[(new@ %a)@]" pp e
    | Swap (l, r) -> fprintf ff "@[<2>(swap@ %a@ %a)@]" pp l pp r
    | Free e -> fprintf ff "@[<2>(free@ %a)@]" pp e

  let string_of = asprintf "%a" pp
end

module Import = struct
  type t = {
    typ : Type.t;
    name : Variable.t;
  }
  [@@deriving eq, ord, sexp, make]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff ({ typ; name } : t) =
    fprintf ff "@[<2>(import@ %a@ as@ %a@,)@]" Type.pp typ Variable.pp name

  let string_of = asprintf "%a" pp
end

module Function = struct
  type t = {
    export : bool;
    name : string;
    param : Binding.t;
    return : Type.t;
    body : Expr.t;
  }
  [@@deriving eq, ord, sexp, make]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp (ff : formatter) ({ export; name; param; return; body } : t) =
    let export_str = if export then "export " else "" in
    fprintf ff "@[<v 0>@[<2>(%sfun %s@ %a :@ %a@ .@]@,@[<v 2>  %a)@]@,@]"
      export_str name Binding.pp param Type.pp return Expr.pp body

  let string_of = asprintf "%a" pp
end

module Module = struct
  type t = {
    imports : Import.t list;
    functions : Function.t list;
    main : Expr.t option;
  }
  [@@deriving eq, ord, sexp, make]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff ({ imports; functions; main } : t) =
    let pp_m_list pp ff xs =
      List.iteri
        ~f:(fun i x ->
          if i > 0 then fprintf ff "@.";
          pp ff x)
        xs
    in
    fprintf ff "@[<v 0>";
    if not (List.is_empty imports) then (
      pp_m_list Import.pp ff imports;
      fprintf ff "@.@.");
    if not (List.is_empty functions) then (
      pp_m_list Function.pp ff functions;
      Option.iter ~f:(fun _ -> fprintf ff "@.") main);
    Option.iter ~f:(fun e -> fprintf ff "%a" Expr.pp e) main;
    fprintf ff "@]"

  let string_of = asprintf "%a" pp
end
