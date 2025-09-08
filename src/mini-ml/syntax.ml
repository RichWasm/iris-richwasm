module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module Type = struct
    type t =
      | Int
      | Var of Variable.t
      | Fun of
        { foralls : Variable.t list
        ; args : t list
        ; ret : t }
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of Variable.t * t
      | Lin of t
    [@@deriving sexp]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t list (* declare the other cases of the sum *)
      | Fun of
        { foralls : Variable.t list
        ; args : (Variable.t * Type.t) list
        ; body : Expr.t }
      [@@deriving sexp]
  end = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t list (* declare the other cases of the sum *)
      | Fun of
        { foralls : Variable.t list
        ; args : (Variable.t * Type.t) list
        ; body : Expr.t }
      [@@deriving sexp]
  end
  and Computation : sig
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Variable.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      [@@deriving sexp]
  end = struct
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Variable.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      [@@deriving sexp]
  end
  and Expr : sig    
    type t =
      | Value of Value.t
      | Computation of Computation.t
      [@@deriving sexp]
  end = struct
    type t =
      | Value of Value.t
      | Computation of Computation.t
      [@@deriving sexp]
  end
end

module Debruijned = struct
  module Variable = struct
    type t = int [@@deriving sexp]
  end

  module Binding = struct
    (* how many variables are being bound here.
       in some cases the one binding is implicit without a [Binding.t] *)
    type t = int [@@deriving sexp]
  end

  module Type = struct
    type t =
      | Int
      | Var of Variable.t
      | Fun of
        { foralls : Binding.t
        ; args : t list
        ; ret : t }
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of t (* for example, [Rec] implicitly binds one variable *)
      | Lin of t
    [@@deriving sexp]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t list (* declare the other cases of the sum *)
      | Fun of
        { foralls : Binding.t
        ; args : Binding.t * Type.t list
        ; body : Expr.t }
      [@@deriving sexp]
  end = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t list (* declare the other cases of the sum *)
      | Fun of
        { foralls : Binding.t
        ; args : Binding.t * Type.t list
        ; body : Expr.t }
      [@@deriving sexp]
  end
  and Computation : sig
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * Expr.t list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      [@@deriving sexp]
  end = struct
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * Expr.t list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      [@@deriving sexp]
  end
  and Expr : sig
    type t =
      | Value of Value.t
      | Computation of Computation.t
      [@@deriving sexp]
  end = struct
    type t =
      | Value of Value.t
      | Computation of Computation.t
      [@@deriving sexp]
  end
end
