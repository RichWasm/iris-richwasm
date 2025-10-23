module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module rec PreType : sig
    type t =
      | Int
      | Var of Variable.t
      | Fun of {
          foralls : Variable.t list;
          arg : Type.t;
          ret : Type.t;
        }
      | Prod of Type.t list
      | Sum of Type.t list
      | Ref of Type.t
      | Rec of Variable.t * Type.t
    [@@deriving sexp, equal]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Fun of {
          foralls : Variable.t list;
          arg : Type.t;
          ret : Type.t;
        }
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

  module Binding = struct
    type t = Variable.t * Type.t [@@deriving sexp]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of {
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : Expr.t;
        }
    [@@deriving sexp]
  end = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of {
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : Expr.t;
        }
    [@@deriving sexp]
  end

  and Expr : sig
    type t =
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Binding.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Binding.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
    [@@deriving sexp]
  end = struct
    type t =
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Binding.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Binding.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
    [@@deriving sexp]
  end

  module Module = struct
    type import = Import of Binding.t [@@deriving sexp]

    type item =
      | Export of Binding.t * Expr.t
      | Private of Binding.t * Expr.t
    [@@deriving sexp]

    type t = Module of import list * item list * Expr.t option
    [@@deriving sexp]
  end
end

module Closed = struct
  module Variable = struct
    type t = string [@@deriving sexp]
  end

  module rec PreType : sig
    type t =
      | Int
      | Var of Variable.t
      | Code of {
          foralls : Variable.t list;
          arg : Type.t;
          ret : Type.t;
        }
      | Prod of Type.t list
      | Sum of Type.t list
      | Ref of Type.t
      | Rec of Variable.t * Type.t
      | Exists of Variable.t * Type.t
    [@@deriving sexp, equal]
  end = struct
    type t =
      | Int
      | Var of Variable.t
      | Code of {
          foralls : Variable.t list;
          arg : Type.t;
          ret : Type.t;
        }
      | Prod of Type.t list
      | Sum of Type.t list
      | Ref of Type.t
      | Rec of Variable.t * Type.t
      | Exists of Variable.t * Type.t
    [@@deriving sexp, equal]
  end

  and Type : sig
    type t = PreType.t [@@deriving sexp, equal]
  end = struct
    type t = PreType.t [@@deriving sexp, equal]
  end

  module Binding = struct
    type t = Variable.t * Type.t [@@deriving sexp]
  end

  module rec Value : sig
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of {
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : Expr.t;
        }
      | Pack of Type.t * Value.t * Type.t
    [@@deriving sexp]
  end = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of {
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : Expr.t;
        }
      | Pack of Type.t * Value.t * Type.t
    [@@deriving sexp]
  end

  and Expr : sig
    type t =
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Binding.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Binding.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      | Unpack of Variable.t * Binding.t * Value.t * Expr.t
    [@@deriving sexp]
  end = struct
    type t =
      | Value of Value.t
      | Apply of Value.t * Type.t list * Value.t
      | Project of int * Value.t
      | Op of [ `Add | `Sub | `Mul | `Div ] * Value.t * Value.t
      | If0 of Value.t * Expr.t * Expr.t
      | Cases of Value.t * (Binding.t * Expr.t) list
      | New of Value.t
      | Deref of Value.t
      | Assign of Value.t * Value.t
      | Let of Binding.t * Expr.t * Expr.t
      | Fold of Type.t * Value.t
      | Unfold of Value.t
      | Unpack of Variable.t * Binding.t * Value.t * Expr.t
    [@@deriving sexp]
  end

  module Module = struct
    type import = Import of Binding.t [@@deriving sexp]

    type item =
      | Export of Binding.t * Expr.t
      | Private of Binding.t * Expr.t
    [@@deriving sexp]

    type t = Module of import list * item list * Expr.t option
    [@@deriving sexp]
  end
end

module Tag = struct
  type t = int [@@deriving sexp, equal]

  let new_counter () : unit -> t =
    let x = ref 0 in
    fun () ->
      let y = !x in
      x := y + 1;
      y
end
