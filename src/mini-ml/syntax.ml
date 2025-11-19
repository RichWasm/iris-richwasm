open! Base

module Source = struct
  module Variable = struct
    type t = string [@@deriving sexp, eq]
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
    [@@deriving sexp, eq]
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
    [@@deriving sexp, eq]
  end

  and Type : sig
    type t = PreType.t [@@deriving sexp, eq]
  end = struct
    type t = PreType.t [@@deriving sexp, eq]
  end

  module Binding = struct
    type t = Variable.t * Type.t [@@deriving sexp]
  end

  module Expr = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Fun of {
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : t;
        }
      | Apply of t * Type.t list * t
      | Project of int * t
      | Op of [ `Add | `Sub | `Mul | `Div ] * t * t
      | If0 of t * t * t
      | Cases of t * (Binding.t * t) list
      | New of t
      | Deref of t
      | Assign of t * t
      | Let of Binding.t * t * t
      | Fold of Type.t * t
      | Unfold of t
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
    type t = string [@@deriving sexp, eq]
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
    [@@deriving sexp, eq]
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
    [@@deriving sexp, eq]
  end

  and Type : sig
    type t = PreType.t [@@deriving sexp, eq]
  end = struct
    type t = PreType.t [@@deriving sexp, eq]
  end

  module Binding = struct
    type t = Variable.t * Type.t [@@deriving sexp]
  end

  module Expr = struct
    type t =
      | Int of int
      | Var of Variable.t
      | Tuple of t list
      | Inj of int * t * Type.t (* declare the other cases of the sum *)
      | Coderef of PreType.t * Variable.t
      | Pack of Type.t * t * Type.t
      | Apply of t * Type.t list * t
      | Project of int * t
      | Op of [ `Add | `Sub | `Mul | `Div ] * t * t
      | If0 of t * t * t
      | Cases of t * (Binding.t * t) list
      | New of t
      | Deref of t
      | Assign of t * t
      | Let of Binding.t * t * t
      | Fold of Type.t * t
      | Unfold of t
      | Unpack of Variable.t * Binding.t * t * t
    [@@deriving sexp]
  end

  module Function = struct
    type t =
      | Function of {
          name : Variable.t;
          foralls : Variable.t list;
          arg : Binding.t;
          ret_type : Type.t;
          body : Expr.t;
        }
    [@@deriving sexp]
  end

  module Module = struct
    type import = Import of Binding.t [@@deriving sexp]

    type item =
      | Export of Binding.t * Function.t
      | Private of Binding.t * Function.t
    [@@deriving sexp]

    type t = Module of import list * item list * Expr.t option
    [@@deriving sexp]
  end
end

module Tag = struct
  type t = int [@@deriving sexp, eq]

  let new_counter () : unit -> t =
    let x = ref 0 in
    fun () ->
      let y = !x in
      x := y + 1;
      y
end
