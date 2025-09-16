module Declosure = struct
  open Sexplib.Std
  open Index

  type typ =
    | Int
    | Prod of typ * typ
    | Ref of typ
    | Lollipop of typ list * typ (* no closures *)
    | Var of int (* type de Bruijn *)
    | Exists of typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binop = Indexed.binop
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type gvar = Indexed.gvar
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of int (* val de Bruijn *)
    | Global of gvar
    | Coderef of gvar
    | Int of int
    | Prod of value * value
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type expr =
    | Val of value
    | App of value * value
    | Let of typ * expr * expr
    | If0 of value * expr * expr
    | Binop of binop * value * value
    | LetPair of typ * typ * expr * expr
    | New of value
    | Swap of value * value
    | Free of value
    | Pack of typ * value * typ
    | Unpack of value * expr * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type import = Import of typ * gvar
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type toplevel =
    | Let of bool * (gvar * typ) * expr (* export *)
    | Func of bool * gvar * typ list * typ * expr
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type modul = Module of import list * toplevel list * expr option
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]
end

module CCErr = struct
  type t
end

module ClosureConversion = struct

end
