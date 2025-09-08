module Source = struct
  module Variable = struct
    type t = string
  end

  module TypeVar = struct
    type t = string
  end

  module rec Type = struct
    type t =
      | Int
      | Var of TypeVar.t
      | Fun of FunType.t
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of TypeVar.t * t
      | LL of t (* TODO: should this be an LL type? *)
  end
  and FunType = struct
    type t =
      { foralls : TypeVar.t list
      ; args : Type.t list
      ; ret : Type.t }
  end

  module rec Value = struct
    type t =
      | Int of int (** FIXME: make this an int31 *)
      | Var of Variable.t
      | Lambda of
          { foralls : TypeVar.t list
          ; args : (Variable.t * Type.t) list
          ; body : Expr.t }
      | Prod of t list
      | Inj of int * t
  end
  and Computation = struct
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Let of Variable.t * Expr.t * Expr.t
      | If0 of Value.t * Expr.t * Expr.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | Cases of Value.t * (int * Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Project of int * Value.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
  end
  and Expr = struct
    type t =
      | Value of Value.t
      | Computation of Computation.t
  end
end

module Tagged = struct
  module Variable = Source.Variable
  module TypeVar = Source.TypeVar

  module Type = struct
    type t = Tag.t * Source.Type.t [@@deriving sexp]
  end
  module FunType = Source.FunType

  module Value = Source.Value
  module Computation = Source.Computation
  module Expr = struct
    type t = Tag.t * Source.Expr.t [@@deriving sexp]
  end

  module Module = struct
    type t = Tag.t * Source.Module.t [@@deriving sexp]
  end
end

module Debruijned = struct
  module Variable = struct
    type t = int [@@deriving sexp]
  end

  module TypeVar = struct
    type t = int [@@driving sexp]
  end

  module rec Type = struct
    type t_base =
      | Int
      | Var of Variable.t
      | Fun of FunType.t
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of TypeVar.t * t
      | LL of t
    and t = Tag.t * t_base [@@deriving sexp]
  end
  and FunType = struct
    type t =
      { foralls : TypeVar.t list
      ; args : Type.t list
      ; ret : Type.t }
    [@@deriving sexp]
  end

  module Value = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Lambda of
          { foralls : TypeVar.t list
          ; args : (Variable.t * Type.t) list
          ; body : Expr.t }
      | Prod of t list
      | Inj of int * t
    [@@deriving sexp]
  end
  and Computation = struct
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Let of Variable.t * Expr.t * Expr.t
      | If0 of Value.t * Expr.t * Expr.t
      | Op of [`Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | Cases of Value.t * (int * Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Project of int * Value.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
  end
  and Expr = struct
    type t_base =
      | Value of Value.t
      | Computation of Computation.t
    and t = Tag.t * t_base [@@deriving sexp]

  module Module = struct
    type import =
      { typ : FunType.t
      ; mod_name : Variable.t
      ; fun_name : Variable.t }
    [@@deriving sexp]

    type func =
      { foralls : TypeVar.t list
      ; args : (Variable.t * Type.t) list
      ; body : Expr.t }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of Variable.t * func * t
      | Global of Variable.t * Expr.t * t
      | Body of Expr.t
    [@@deriving sexp]
  end

  module Module = struct
    type import =
      { typ : FunType.t
      ; mod_name : Variable.t
      ; fun_name : Variable.t }
    [@@deriving sexp]

    type func =
      { foralls : TypeVar.t list
      ; args : (Variable.t * Type.t) list
      ; body : Expr.t }
    [@@deriving sexp]

    type t =
      | LetIm of import * t
      | LetEx of Variable.t * func * t
      | Global of Variable.t * Expr.t * t
      | Body of Expr.t
    [@@deriving sexp]
  end
end
