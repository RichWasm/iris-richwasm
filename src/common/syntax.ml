open! Base

module Copyability = struct
  type t =
    | NoCopy
    | ExCopy
    | ImCopy
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Dropability = struct
  type t =
    | NoDrop
    | ExDrop
    | ImDrop
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Memory = struct
  type t =
    | MM
    | GC
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module PrimitiveRep = struct
  type t =
    | Ptr
    | I32
    | I64
    | F32
    | F64
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Representation = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Prim of PrimitiveRep.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Size = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Rep of Representation.t
    | Const of int
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Sizity = struct
  type t =
    | Sized of Size.t
    | Unsized
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Kind = struct
  type t =
    | VALTYPE of Representation.t * Copyability.t * Dropability.t
    | MEMTYPE of Sizity.t * Memory.t * Dropability.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Quantifier = struct
  type t =
    | Memory
    | Representation
    | Size
    | Type of Kind.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Sign = struct
  type t =
    | Unsigned
    | Signed
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Int = struct
  module Type = struct
    type t =
      | I32
      | I64
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Unop = struct
    type t =
      | Clz
      | Ctz
      | Popcnt
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Binop = struct
    type t =
      | Add
      | Sub
      | Mul
      | Div
      | Rem
      | And
      | Or
      | Xor
      | Shl
      | Shr
      | Rotl
      | Rotr
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Testop = struct
    type t = Eqz [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Relop = struct
    type t =
      | Eq
      | Ne
      | Lt
      | Gt
      | Le
      | Ge
    [@@deriving eq, ord, iter, map, fold, sexp]
  end
end

module Float = struct
  module Type = struct
    type t =
      | F32
      | F64
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Unop = struct
    type t =
      | Neg
      | Abs
      | Ceil
      | Floor
      | Trunc
      | Nearest
      | Sqrt
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Binop = struct
    type t =
      | Add
      | Sub
      | Mul
      | Div
      | Min
      | Max
      | CopySign
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Relop = struct
    type t =
      | Eq
      | Ne
      | Lt
      | Gt
      | Le
      | Ge
    [@@deriving eq, ord, iter, map, fold, sexp]
  end
end

module NumType = struct
  type t =
    | Int of Int.Type.t
    | Float of Float.Type.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module ConversionOp = struct
  type t =
    | Wrap
    | Extend of Sign.t
    | Trunc of Int.Type.t * Float.Type.t * Sign.t
    | TruncSat of Int.Type.t * Float.Type.t * Sign.t
    | Demote
    | Promote
    | Convert of Float.Type.t * Int.Type.t * Sign.t
    | ReinterpretFI of Float.Type.t * Int.Type.t
    | ReinterpretIF of Int.Type.t * Float.Type.t
    | ReinterpretII of Int.Type.t * Sign.t * Sign.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module NumInstruction = struct
  type t =
    | Int1 of Int.Type.t * Int.Unop.t
    | Int2 of Int.Type.t * Int.Binop.t
    | IntTest of Int.Type.t * Int.Testop.t
    | IntRel of Int.Type.t * Int.Relop.t
    | Float1 of Float.Type.t * Float.Unop.t
    | Float2 of Float.Type.t * Float.Binop.t
    | FloatRel of Float.Type.t * Float.Relop.t
    | Cvt of ConversionOp.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module rec Type : sig
  type t =
    | Var of int
    | Num of NumType.t
    | Sum of t list
    | Prod of t list
    | Ref of Memory.t * t
    | GCPtr of t
    | CodeRef of FunctionType.t
    | Rep of Representation.t * t
    | Pad of Size.t * t
    | Ser of t
    | Rec of t
    | Exists of Quantifier.t * t
  [@@deriving eq, ord, iter, map, fold, sexp]
end = struct
  type t =
    | Var of int
    | Num of NumType.t
    | Sum of t list
    | Prod of t list
    | Ref of Memory.t * t
    | GCPtr of t
    | CodeRef of FunctionType.t
    | Rep of Representation.t * t
    | Pad of Size.t * t
    | Ser of t
    | Rec of t
    | Exists of Quantifier.t * t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

and InstructionType : sig
  type t = InstructionType of Type.t list * Type.t list
  [@@deriving eq, ord, iter, map, fold, sexp]
end = struct
  type t = InstructionType of Type.t list * Type.t list
  [@@deriving eq, ord, iter, map, fold, sexp]
end

and FunctionType : sig
  type t = FunctionType of Quantifier.t list * InstructionType.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end = struct
  type t = FunctionType of Quantifier.t list * InstructionType.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Index = struct
  type t =
    | Mem of Memory.t
    | Rep of Representation.t
    | Size of Size.t
    | Type of Type.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module LocalFx = struct
  type t = LocalFx of (int * Type.t) list
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Path = struct
  module Component = struct
    type t =
      | Proj of int
      | Unwrap
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  type t = Path of Component.t list
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Instruction = struct
  type t =
    | Nop
    | Unreachable
    | Copy
    | Drop
    | Num of NumInstruction.t
    | NumConst of NumType.t * int
    | Block of InstructionType.t * LocalFx.t * t list
    | Loop of InstructionType.t * t list
    | Ite of InstructionType.t * LocalFx.t * t list * t list
    | Br of int
    | BrIf of int
    | BrTable of int list * int
    | Return
    | LocalGet of int
    | LocalSet of int
    | GlobalGet of int
    | GlobalSet of int
    | GlobalSwap of int
    | CodeRef of int
    | Inst of Index.t
    | Call of int * Index.t list
    | CallIndirect
    | Inject of int * Type.t list
    | Case of InstructionType.t * LocalFx.t * t list list
    | Group of int
    | Ungroup
    | Fold of Type.t
    | Unfold
    | Pack of Index.t * Type.t
    | Unpack of InstructionType.t * LocalFx.t * t list
    | Wrap of Type.t
    | Unwrap
    | RefNew of Memory.t * Type.t
    | RefLoad of Path.t * Type.t
    | RefStore of Path.t
    | RefSwap of Path.t
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Mutability = struct
  type t =
    | Mut
    | Imm
  [@@deriving eq, ord, iter, map, fold, sexp]
end

module Module = struct
  module Import = struct
    module Desc = struct
      type t =
        | ImFunction of FunctionType.t
        | ImGlobal of Mutability.t * Type.t
      [@@deriving eq, ord, iter, map, fold, sexp]
    end

    type t = {
      name : string;
      desc : Desc.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Global = struct
    type t = {
      mut : Mutability.t;
      typ : Type.t;
      init : Instruction.t list;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Function = struct
    type t = {
      typ : FunctionType.t;
      locals : Representation.t list;
      body : Instruction.t list;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  module Export = struct
    module Desc = struct
      type t =
        | ExFunction of int
        | ExGlobal of int
      [@@deriving eq, ord, iter, map, fold, sexp]
    end

    type t = {
      name : string;
      desc : Desc.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]
  end

  type t = {
    imports : Import.t list;
    globals : Global.t list;
    functions : Function.t list;
    table : int list;
    start : int option;
    exports : Export.t list;
  }
  [@@deriving eq, ord, iter, map, fold, sexp]
end
