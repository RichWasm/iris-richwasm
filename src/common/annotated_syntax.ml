open! Base
open Stdlib.Format

module Path = struct
  module Component = struct
    type t = [%import: Richwasm_extract.RwSyntax.path_component]
    [@@deriving eq, ord]
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.path[@with path_component := Component.t])]
  [@@deriving eq, ord]
end

module ConcreteMemory = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.concrete_memory]
  [@@deriving eq, ord]
end

module Copyability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.copyability]
  [@@deriving eq, ord]
end

module Dropability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.dropability]
  [@@deriving eq, ord]
end

module PrimitiveRep = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.primitive_rep]
  [@@deriving eq, ord]
end

module Sign = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.sign] [@@deriving eq, ord]
end

module Float = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_type]
    [@@deriving eq, ord]
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_unop]
    [@@deriving eq, ord]
  end

  module Binop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_binop]
    [@@deriving eq, ord]
  end

  module Relop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_relop]
    [@@deriving eq, ord]
  end
end

module Int = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_type]
    [@@deriving eq, ord]
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_unop]
    [@@deriving eq, ord]
  end

  module Binop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_binop[@with sign := Sign.t])]
    [@@deriving eq, ord]
  end

  module Relop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_relop[@with sign := Sign.t])]
    [@@deriving eq, ord]
  end

  module Testop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_testop]
    [@@deriving eq, ord]
  end
end

module NumType = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.num_type
      [@with
        int_type := Int.Type.t;
        float_type := Float.Type.t])]
  [@@deriving eq, ord]
end

module ConversionOp = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.conversion_op
      [@with
        sign := Sign.t;
        int_type := Int.Type.t;
        float_type := Float.Type.t;
        num_type := NumType.t])]
  [@@deriving eq, ord]
end

module NumInstruction = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.num_instruction
      [@with
        int_type := Int.Type.t;
        int_unop := Int.Unop.t;
        int_binop := Int.Binop.t;
        int_testop := Int.Testop.t;
        int_relop := Int.Relop.t;
        float_type := Float.Type.t;
        float_unop := Float.Unop.t;
        float_binop := Float.Binop.t;
        float_relop := Float.Relop.t;
        conversion_op := ConversionOp.t])]
  [@@deriving eq, ord]
end

module Representation = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.representation
      [@with primitive_rep := PrimitiveRep.t])]
  [@@deriving eq, ord]
end

module Size = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.size
      [@with representation := Representation.t])]
  [@@deriving eq, ord]
end

module Sizity = struct
  type t =
    [%import: (Richwasm_extract.RwSyntax.Core.sizity[@with size := Size.t])]
  [@@deriving eq, ord]
end

module Memory = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.memory
      [@with concrete_memory := ConcreteMemory.t])]
  [@@deriving eq, ord]
end

module Kind = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.kind
      [@with
        representation := Representation.t;
        copyability := Copyability.t;
        dropability := Dropability.t;
        sizity := Sizity.t;
        memory := Memory.t])]
  [@@deriving eq, ord]
end

(* work around bug? with ppx_import *)
module Internal = struct
  module Types = struct
    type typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.coq_type
        [@with
          kind := Kind.t;
          num_type := NumType.t;
          memory := Memory.t;
          representation := Representation.t;
          size := Size.t;
          coq_type := typ;
          function_type := function_typ])]

    and function_typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.function_type
        [@with
          kind := Kind.t;
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving eq, ord]

    type instruction_typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.instruction_type
        [@with
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving eq, ord]
  end
end

module Type = struct
  include Internal.Types

  type t = Internal.Types.typ [@@deriving eq, ord]
end

module InstructionType = struct
  include Internal.Types

  type t = Internal.Types.instruction_typ [@@deriving eq, ord]
end

module FunctionType = struct
  include Internal.Types

  type t = Internal.Types.function_typ [@@deriving eq, ord]
end

module Index = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.index
      [@with
        memory := Memory.t;
        representation := Representation.t;
        size := Size.t;
        coq_type := Type.t;
        instruction_type := InstructionType.t;
        function_type := FunctionType.t])]
  [@@deriving eq, ord]
end

module Instruction = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.instruction
      [@with
        instruction_type := InstructionType.t;
        num_instruction := NumInstruction.t;
        coq_type := Type.t;
        index := Index.t;
        path := Path.t])]
  [@@deriving eq, ord]
end

module Module = struct
  module Function = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.module_function
        [@with
          Core.function_type := FunctionType.t;
          Core.representation := Representation.t;
          Core.instruction := Instruction.t])]
    [@@deriving eq, ord]
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.module0
      [@with
        Core.function_type := FunctionType.t;
        module_function := Function.t])]
  [@@deriving eq, ord]
end
