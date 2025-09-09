open Sexplib.Std

module Types = struct
  type variable = string
  [@@deriving show { with_path = false }, eq, sexp]

  type typ =
    | Int
    | Lolipop of typ * typ
    | Prod of typ * typ
    | Ref of typ
  [@@deriving show { with_path = false }, eq, sexp]

  type value =
    | Var of variable
    | Int of int
    | Lam of (variable * typ) list * typ
    | Prod of value * value
  [@@deriving show { with_path = false }, eq, sexp]

  type expr =
    | Val of value
    | App of value * value
    | Let of variable * expr * expr
    | If0 of value * expr * expr
    | Binop of [`Add | `Sub | `Mul | `Div] * value * value
    | LetPair of variable * variable * expr * expr
    | New of value
    | Swap of value * value
    | Free of value
  [@@deriving show { with_path = false }, eq, sexp]
end

module Variable = struct
  type t = Types.variable
  [@@deriving show, eq, sexp]
end

module Val = struct
  type t = Types.value
  [@@deriving show, eq, sexp]
end

module Expr = struct
  type t = Types.expr
  [@@deriving show, eq, sexp]
end

module Type = struct
  type t = Types.typ
  [@@deriving show, eq, sexp]
end
