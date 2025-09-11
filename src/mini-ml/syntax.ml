module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module rec PreType : sig
    type t =
      | Int
      | Var of Variable.t
      | Fun of
          { foralls: Variable.t list;
            args: Type.t list;
            ret: Type.t }
      | Prod of Type.t list
      | Sum of Type.t list
      | Ref of Type.t
      | Rec of Variable.t * Type.t
    [@@deriving sexp, equal]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Fun of
          { foralls: Variable.t list;
            args: Type.t list;
            ret: Type.t }
      | Prod of Type.t list
      | Sum of Type.t list
      | Ref of Type.t
      | Rec of Variable.t * Type.t
    [@@deriving sexp, equal]
  end

  and Type : sig
    type t = PreType.t [@@deriving sexp, equal]
  end = struct
    type t = PreType.t [@@deriving sexp, equal]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of
          { foralls: Variable.t list;
            args: (Variable.t * Type.t) list;
            body: Expr.t }
    [@@deriving sexp]
  end = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of
          { foralls: Variable.t list;
            args: (Variable.t * Type.t) list;
            body: Expr.t }
    [@@deriving sexp]
  end

  and Expr : sig
    type t =
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [`Add | `Sub | `Mul | `Div] * Value.t * Value.t
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
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t list
      | Project of int * Value.t
      | Op of [`Add | `Sub | `Mul | `Div] * Value.t * Value.t
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
end
