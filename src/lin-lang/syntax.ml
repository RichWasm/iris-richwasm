open! Base
open Stdlib.Format

module Internal = struct
  let pp_list pp sep xs =
    List.iteri
      ~f:(fun i x ->
        if i > 0 then sep ();
        pp x)
      xs
end

module Variable = struct
  type t = string [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff = fprintf ff "@[%s@]"
  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Type = struct
  type t =
    | Int
    | Lollipop of t * t
    | Prod of t list
    | Sum of t list
    | Ref of t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let rec pp ff : t -> unit =
    let pp_sep ~(sep : string) ts =
      fprintf ff "@[(";
      Internal.pp_list
        (fun x -> fprintf ff "%a" pp x)
        (fun () -> fprintf ff "@ %s@ " sep)
        ts;
      fprintf ff ")@]"
    in
    function
    | Int -> fprintf ff "@[int@]"
    | Lollipop (t1, t2) -> fprintf ff "@[(%a@ ⊸@ %a)@]" pp t1 pp t2
    | Prod ts -> pp_sep ~sep:"⊗" ts
    | Sum ts -> pp_sep ~sep:"⊕" ts
    | Ref t -> fprintf ff "@[(ref@ %a)@]" pp t

  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Binding = struct
  type t = Variable.t * Type.t [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff ((x, t) : t) = fprintf ff "@[(%a@ :@ %a)@]" Variable.pp x Type.pp t
  let string_of = asprintf "%a" pp
end

module Binop = struct
  type t =
    | Add
    | Sub
    | Mul
    | Div
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff : t -> unit = function
    | Add -> fprintf ff "+"
    | Sub -> fprintf ff "-"
    | Mul -> fprintf ff "×"
    | Div -> fprintf ff "÷"

  let string_of = asprintf "%a" pp
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module rec Value : sig
  type t =
    | Var of Variable.t
    | Int of int
    | Lam of Binding.t * Type.t * Expr.t
    | Tuple of t list
    | Inj of int * t * Type.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
  val string_of : t -> string
end = struct
  type t =
    | Var of Variable.t
    | Int of int
    | Lam of Binding.t * Type.t * Expr.t
    | Tuple of t list
    | Inj of int * t * Type.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff : t -> unit = function
    | Var x -> Variable.pp ff x
    | Int n -> fprintf ff "%d" n
    | Lam (bind, ret, body) ->
        fprintf ff "@[<v 2>@[<2>(λ@ %a@ :@ %a@ @].@;@[<2>%a@])@]@]" Binding.pp
          bind Type.pp ret Expr.pp body
    | Tuple vs ->
        fprintf ff "@[<2>(";
        Internal.pp_list
          (fun x -> fprintf ff "%a" pp x)
          (fun () -> fprintf ff ",@ ")
          vs;
        fprintf ff ")@]"
    | Inj (i, v, t) ->
        fprintf ff "@[(inj %a %a@ :@ %a)" Int.pp i Value.pp v Type.pp t

  let string_of = asprintf "%a" pp
end

and Expr : sig
  type t =
    | Val of Value.t
    | App of Value.t * Value.t
    | Let of Binding.t * Expr.t * Expr.t
    | Split of Binding.t list * Expr.t * Expr.t
    | Cases of Value.t * (Binding.t * t) list
    | If0 of Value.t * Expr.t * Expr.t
    | Binop of Binop.t * Value.t * Value.t
    | New of Value.t
    | Swap of Value.t * Value.t
    | Free of Value.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
  val string_of : t -> string
end = struct
  type t =
    | Val of Value.t
    | App of Value.t * Value.t
    | Let of Binding.t * Expr.t * Expr.t
    | Split of Binding.t list * Expr.t * Expr.t
    | Cases of Value.t * (Binding.t * t) list
    | If0 of Value.t * Expr.t * Expr.t
    | Binop of Binop.t * Value.t * Value.t
    | New of Value.t
    | Swap of Value.t * Value.t
    | Free of Value.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff (e : t) =
    match e with
    | Val v -> Value.pp ff v
    | App (l, r) -> fprintf ff "@[<2>(app@ %a@ %a)@]" Value.pp l Value.pp r
    | Let (bind, e, body) ->
        fprintf ff "@[<v 0>@[<2>(let@ %a@ =@ %a@ in@]@;@[<2>%a)@]@]" Binding.pp
          bind pp e pp body
    | Split (bs, e, b) ->
        fprintf ff "@[<v 0>@[<2>(split@ (";
        Internal.pp_list
          (fun x -> fprintf ff "%a" Binding.pp x)
          (fun () -> fprintf ff ",@ ")
          bs;
        fprintf ff ")@ =@ %a@ in@]@;@[<2>%a)@]@]" pp e pp b
    | Cases (scrutinee, cases) ->
        fprintf ff "@[<v 2>@[<2>(cases %a@]@;" Value.pp scrutinee;
        Internal.pp_list
          (fun (binding, body) ->
            fprintf ff "@[<2>(case %a@ %a)@]" Binding.pp binding pp body)
          (fun () -> fprintf ff "@;")
          cases;
        fprintf ff "@[<2>)@]@]"
    | If0 (v, e1, e2) ->
        fprintf ff "@[<2>(if %a@;then %a@;else@ %a)@]" Value.pp v pp e1 pp e2
    | Binop (op, l, r) ->
        fprintf ff "@[<2>(%a@ %a@ %a)@]" Value.pp l Binop.pp op Value.pp r
    | New v -> fprintf ff "@[<2>(new@ %a)@]" Value.pp v
    | Swap (l, r) -> fprintf ff "@[<2>(swap@ %a@ %a)@]" Value.pp l Value.pp r
    | Free v -> fprintf ff "@[<2>(free@ %a)@]" Value.pp v

  let string_of = asprintf "%a" pp
end

module Import = struct
  type t = {
    typ : Type.t;
    name : Variable.t;
  }
  [@@deriving eq, ord, iter, map, fold, sexp, make]

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
  [@@deriving eq, ord, iter, map, fold, sexp, make]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp (ff : formatter) ({ export; name; param; return; body } : t) =
    let export_str = if export then "export " else "" in
    fprintf ff "@[<2>(%sfun %s@ %a :@ %a@ .@ %a)@;@]" export_str name Binding.pp
      param Type.pp return Expr.pp body

  let string_of = asprintf "%a" pp
end

module Module = struct
  type t = {
    imports : Import.t list;
    functions : Function.t list;
    main : Expr.t option;
  }
  [@@deriving eq, ord, iter, map, fold, sexp, make]

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
      fprintf ff "@.@.");
    Option.iter ~f:(fun e -> fprintf ff "%a" Expr.pp e) main;
    fprintf ff "@]"

  let string_of = asprintf "%a" pp
end
