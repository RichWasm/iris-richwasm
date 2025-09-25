open! Base
open Stdlib.Format

module Big_int_Z = struct
  include Z

  let pp fmt z = Stdlib.Format.fprintf fmt "%s" (Z.to_string z)
  let sexp_of_t z = Sexp.Atom (Z.to_string z)

  let t_of_sexp = function
    | Sexp.Atom s -> Z.of_string s
    | _ -> failwith "expected atom"
end

module Path = struct
  module Component = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.path_component[@with Z.t := Big_int_Z.t])]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.path[@with path_component := Component.t])]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module ConcreteMemory = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.concrete_memory]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Copyability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.copyability]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Dropability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.dropability]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module PrimitiveRep = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.primitive_rep]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Sign = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.sign]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff : t -> unit = function
    | SignU -> fprintf ff "u"
    | SignS -> fprintf ff "s"
end

module Float = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_type]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | F32T -> fprintf ff "f32"
      | F64T -> fprintf ff "f64"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_unop]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | NegF -> fprintf ff "neg"
      | AbsF -> fprintf ff "abs"
      | CeilF -> fprintf ff "ceil"
      | FloorF -> fprintf ff "floor"
      | TruncF -> fprintf ff "trunc"
      | NearestF -> fprintf ff "nearest"
      | SqrtF -> fprintf ff "sqrt"
  end

  module Binop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_binop]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | AddF -> fprintf ff "add"
      | SubF -> fprintf ff "sub"
      | MulF -> fprintf ff "mul"
      | DivF -> fprintf ff "div"
      | MinF -> fprintf ff "min"
      | MaxF -> fprintf ff "max"
      | CopySignF -> fprintf ff "copysign"
  end

  module Relop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_relop]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | EqF -> fprintf ff "eq"
      | NeF -> fprintf ff "ne"
      | LtF -> fprintf ff "lt"
      | GtF -> fprintf ff "gt"
      | LeF -> fprintf ff "le"
      | GeF -> fprintf ff "ge"
  end
end

module Int = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_type]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | I32T -> fprintf ff "i32"
      | I64T -> fprintf ff "i64"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_unop]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | ClzI -> fprintf ff "clz"
      | CtzI -> fprintf ff "ctz"
      | PopcntI -> fprintf ff "popcnt"
  end

  module Binop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_binop[@with sign := Sign.t])]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | AddI -> fprintf ff "add"
      | SubI -> fprintf ff "sub"
      | MulI -> fprintf ff "mul"
      | DivI s -> fprintf ff "div_%a" Sign.pp s
      | RemI s -> fprintf ff "rem_%a" Sign.pp s
      | AndI -> fprintf ff "and"
      | OrI -> fprintf ff "or"
      | XorI -> fprintf ff "xor"
      | ShlI -> fprintf ff "shl"
      | ShrI s -> fprintf ff "shr_%a" Sign.pp s
      | RotlI -> fprintf ff "rotl"
      | RotrI -> fprintf ff "rotr"
  end

  module Relop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_relop[@with sign := Sign.t])]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | EqI -> fprintf ff "eq"
      | NeI -> fprintf ff "ne"
      | LtI s -> fprintf ff "lt_%a" Sign.pp s
      | GtI s -> fprintf ff "gt_%a" Sign.pp s
      | LeI s -> fprintf ff "le_%a" Sign.pp s
      | GeI s -> fprintf ff "ge_%a" Sign.pp s
  end

  module Testop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_testop]
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff : t -> unit = function
      | EqzI -> fprintf ff "eqz"
  end
end

module ConversionOp = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.conversion_op
      [@with
        sign := Sign.t;
        int_type := Int.Type.t;
        float_type := Float.Type.t])]
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | CWrap -> fprintf ff "i32.wrap_i64"
    | CExtend s -> fprintf ff "i64.extend_i32_%a" Sign.pp s
    (* | CTrunc (int_type, float_type, sign) -> failwith "TODO"
    | CTruncSat (int_type, float_type, sign) -> failwith "TODO" *)
    | CDemote -> fprintf ff "f32.demote_f64"
    | CPromote -> fprintf ff "f64.promote_f32"
    (* | CConvert (float_type, int_type, sign) -> failwith "TODO, ordering"
    | CReinterpretFI (float_type, int_type) -> failwith "TODO"
    | CReinterpretIF (int_type, float_type) -> failwith "TODO"
    | CReinterpretII (int_type, sign1, sign2) -> failwith "TODO" *)
    | x -> pp_sexp ff x
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
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp ff : t -> unit = function
    | IInt1 (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Unop.pp o
    | IInt2 (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Binop.pp o
    | IIntTest (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Testop.pp o
    | IIntRel (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Relop.pp o
    | IFloat1 (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Unop.pp o
    | IFloat2 (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Binop.pp o
    | IFloatRel (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Relop.pp o
    | ICvt o -> fprintf ff "%a" ConversionOp.pp o
end

module Representation = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.representation
      [@with
        Z.t := Big_int_Z.t;
        primitive_rep := PrimitiveRep.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module Size = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.size
      [@with
        Z.t := Big_int_Z.t;
        representation := Representation.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module Sizity = struct
  type t =
    [%import: (Richwasm_extract.RwSyntax.Core.sizity[@with size := Size.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module Memory = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.memory
      [@with
        Z.t := Big_int_Z.t;
        concrete_memory := ConcreteMemory.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
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
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module NumType = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.num_type
      [@with
        int_type := Int.Type.t;
        float_type := Float.Type.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp ff : t -> unit = function
    | IntT it -> Int.Type.pp ff it
    | FloatT ft -> Float.Type.pp ff ft
end

(* work around bug? with ppx_import *)
module Internal = struct
  module Types = struct
    type typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.coq_type
        [@with
          Z.t := Big_int_Z.t;
          kind := Kind.t;
          num_type := NumType.t;
          memory := Memory.t;
          representation := Representation.t;
          size := Size.t;
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving show { with_path = false }]

    and instruction_typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.instruction_type
        [@with
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving show { with_path = false }]

    and function_typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.function_type
        [@with
          kind := Kind.t;
          instruction_type := instruction_typ;
          function_type := function_typ])]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
  end
end

module Type = struct
  include Internal.Types

  type t = Internal.Types.typ
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module InstructionType = struct
  include Internal.Types

  type t = Internal.Types.instruction_typ
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff (InstrT (from, res) : t) : unit =
    fprintf ff "(@[";
    List.iter ~f:(fprintf ff "%a@ " Type.pp) from;
    fprintf ff "->";
    List.iter ~f:(fprintf ff "@ %a" Type.pp) res;
    fprintf ff "@])"
end

module FunctionType = struct
  include Internal.Types

  type t = Internal.Types.function_typ
  [@@deriving eq, ord, iter, map, fold, sexp]

  let rec pp ff : t -> unit = function
    | MonoFunT it -> InstructionType.pp ff it
    | ForallMemT ft -> fprintf ff "(forall.mem %a)" pp ft
    | ForallRepT ft -> fprintf ff "(forall.rep %a)" pp ft
    | ForallSizeT ft -> fprintf ff "(forall.size %a)" pp ft
    | ForallTypeT (k, ft) -> fprintf ff "(forall.size %a %a)" Kind.pp k pp ft
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
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
end

module LocalFx = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.local_fx
      [@with
        Z.t := Big_int_Z.t;
        coq_type := Type.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_ ff (lfx : t) : unit =
    failwith "TODO";
    fprintf ff "";
    List.iter ~f:(fun (i, t) -> fprintf ff "") lfx;
    fprintf ff ""
end

module Instruction = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.instruction
      [@with
        Z.t := Big_int_Z.t;
        instruction_type := InstructionType.t;
        num_instruction := NumInstruction.t;
        local_fx := LocalFx.t;
        index := Index.t;
        path := Path.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let show_pp = pp

  let rec pp ff : t -> unit =
    let pp_instrs ff (instrs : t list) = () in
    function
    | INop _ -> fprintf ff "nop"
    | IUnreachable _ -> fprintf ff "unreachable"
    | ICopy _ -> fprintf ff "copy"
    | IDrop _ -> fprintf ff "drop"
    | INum (_, ni) -> fprintf ff "%a" NumInstruction.pp ni
    | INumConst (InstrT ([], [ NumT (_, t) ]), n) ->
        fprintf ff "%a.const %a" NumType.pp t Big_int_Z.pp n
        (*| IBlock (it, lfx, instrs) ->
        (* TODO: block return *)
        fprintf ff "block %a %a @; @[<v 2>%a@] end" InstructionType.pp it
          LocalFx.pp lfx pp_instrs instrs *)
    | IReturn _ -> fprintf ff "return"
    | ILocalGet (_, i) -> fprintf ff "local.get %a" Big_int_Z.pp i
    | ILocalSet (_, i) -> fprintf ff "local.set %a" Big_int_Z.pp i
    | IGlobalGet (_, i) -> fprintf ff "global.get %a" Big_int_Z.pp i
    | IGlobalSet (_, i) -> fprintf ff "global.set %a" Big_int_Z.pp i
    | IGlobalSwap (_, i) -> fprintf ff "global.swap %a" Big_int_Z.pp i
    | x -> show_pp ff x
end

module Module = struct
  module Mutability = struct
    type t = [%import: Richwasm_extract.RwSyntax.mutability]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
  end

  module Function = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.module_function
        [@with
          Core.function_type := FunctionType.t;
          Core.representation := Representation.t;
          Core.instruction := Instruction.t])]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

    let pp ff ({ mf_type; mf_body } : t) : unit =
      (* FIXME: where are locals?? *)
      fprintf ff "@[<v 2>@[(func %a@]" FunctionType.pp mf_type;
      List.iter ~f:(fprintf ff "@;%a" Instruction.pp) mf_body;
      fprintf ff "@[)@]@]"
  end

  module Global = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.module_global
        [@with
          mutability := Mutability.t;
          Core.coq_type := Type.t;
          Core.instruction := Instruction.t])]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
  end

  module Import = struct
    module Desc = struct
      type t =
        [%import:
          (Richwasm_extract.RwSyntax.module_import_desc
          [@with
            Core.function_type := FunctionType.t;
            Core.coq_type := Type.t;
            mutability := Mutability.t])]
      [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
    end

    type t =
      [%import:
        (Richwasm_extract.RwSyntax.module_import
        [@with module_import_desc := Desc.t])]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
  end

  module Export = struct
    module Desc = struct
      type t =
        [%import:
          (Richwasm_extract.RwSyntax.module_export_desc
          [@with Z.t := Big_int_Z.t])]
      [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
    end

    type t =
      [%import:
        (Richwasm_extract.RwSyntax.module_export
        [@with module_export_desc := Desc.t])]
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.module0
      [@with
        module_import := Import.t;
        module_global := Global.t;
        module_function := Function.t;
        Z.t := Big_int_Z.t;
        module_export := Export.t])]
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff ({ m_imports; m_globals; m_funcs; m_table; m_start; m_exports } : t)
      : unit =
    let print_sep ~f ~sep lst =
      List.iter
        ~f:(fun x ->
          sep ();
          f x)
        lst
    in
    let space_hint () = fprintf ff "@ " in
    let break_hint () = fprintf ff "@;" in

    fprintf ff "@[<v 2>@[(module @]";
    print_sep ~f:(Import.pp ff) ~sep:break_hint m_imports;
    print_sep ~f:(Global.pp ff) ~sep:break_hint m_globals;
    print_sep ~f:(Function.pp ff) ~sep:break_hint m_funcs;
    fprintf ff "@;@[(table@[<hv 2>";
    if List.is_empty m_table then () else fprintf ff "@ ";
    print_sep ~f:(Big_int_Z.pp ff) ~sep:space_hint m_table;
    fprintf ff "@])@]";
    Option.iter
      ~f:(fun start -> fprintf ff "@;(start %a)" Big_int_Z.pp start)
      m_start;
    print_sep ~f:(Export.pp ff) ~sep:break_hint m_exports;
    fprintf ff "@])@]"
end
