module Types = struct
  open Sexplib.Std

  type variable = string
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type typ =
    | Int
    | Prod of typ * typ
    | Ref of typ
    | Lolipop of typ * typ
    | Var of variable
    | Exists of variable * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binding = variable * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of variable
    | Coderef of variable
    | Int of int
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
    | Pack of typ * value * value
    | Unpack of variable * binding * value * expr
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type import = Import of typ * variable
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type toplevel =
    | Let of bool * binding * expr (* export *)
    | Func of bool * variable * binding list * typ * expr
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type modul = Module of import list * toplevel list * expr option
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]
end
