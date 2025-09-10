open Base

module Tag = struct
  type t = int [@@deriving sexp, equal]

  let new_counter () : unit -> t =
    let x = ref 0 in
    fun () ->
      let y = !x in
      x := !x + 1 ;
      y
end

module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module TypeVar = struct
    type t = string [@@deriving sexp]
  end

  module rec Type : sig
    type t =
      | Int
      | Var of TypeVar.t
      | Fun of FunType.t
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of TypeVar.t * t
      | LL of t (* TODO: should this be an LL type? *)
  end = struct
    type t =
      | Int
      | Var of TypeVar.t
      | Fun of FunType.t
      | Prod of t list
      | Sum of t list
      | Ref of t
      | Rec of TypeVar.t * t
      | LL of t (* TODO: should this be an LL type? *)
    [@@deriving sexp]
  end

  and FunType : sig
    type t = {foralls: TypeVar.t list; args: Type.t list; ret: Type.t}
  end = struct
    type t = {foralls: TypeVar.t list; args: Type.t list; ret: Type.t}
    [@@deriving sexp]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Lambda of
          { foralls: TypeVar.t list
          ; args: (Variable.t * Type.t) list
          ; body: Expr.t }
      | Prod of t list
      | Inj of int * t
  end = struct
    type t =
      | Int of int  (** FIXME: make this an int31 *)
      | Var of Variable.t
      | Lambda of
          { foralls: TypeVar.t list
          ; args: (Variable.t * Type.t) list
          ; body: Expr.t }
      | Prod of t list
      | Inj of int * t
    [@@deriving sexp]
  end

  and Computation : sig
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Let of Variable.t * Expr.t * Expr.t
      | If0 of Value.t * Expr.t * Expr.t
      | Op of [`Add | `Sub | `Mul | `Div] * Value.t * Value.t
      | Cases of Value.t * (int * Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Project of int * Value.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
  end = struct
    type t =
      | Apply of Value.t * Type.t list * Value.t list
      | Let of Variable.t * Expr.t * Expr.t
      | If0 of Value.t * Expr.t * Expr.t
      | Op of [`Add | `Sub | `Mul | `Div] * Value.t * Value.t
      | Cases of Value.t * (int * Variable.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Project of int * Value.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
    [@@deriving sexp]
  end

  and Expr : sig
    type t = Value of Value.t | Computation of Computation.t
  end = struct
    type t = Value of Value.t | Computation of Computation.t [@@deriving sexp]
  end

  and Module : sig
    type t
  end = struct
    type t
  end
end
