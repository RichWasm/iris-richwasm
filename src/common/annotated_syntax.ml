open! Base
open Stdlib.Format

let pp_roqc_list (pp : formatter -> 'a -> unit) ff (lst : 'a list) =
  fprintf ff "@[<v 0>[@[<hv 2>";
  List.iteri
    ~f:(fun i x ->
      if i <> 0 then fprintf ff ";@ ";
      fprintf ff "%a" pp x)
    lst;
  fprintf ff "@]]@]"

let pp_roqc_option (pp : formatter -> 'a -> unit) ff = function
  | Some x -> fprintf ff "(Some %a)" pp x
  | None -> fprintf ff "None"

module Z' = struct
  include Z

  let sexp_of_t z = Sexp.Atom (Z.to_string z)

  let t_of_sexp = function
    | Sexp.Atom s -> Z.of_string s
    | _ -> failwith "expected atom"
end

module Path = struct
  module Component = struct
    type t =
      [%import: (Richwasm_extract.RwSyntax.path_component[@with Z.t := Z'.t])]
    [@@deriving eq, ord, sexp]

    let pp_roqc ff : t -> unit = function
      | PCProj i -> fprintf ff "(PCProj %a)" Z.pp_print i
      | PCSkip -> fprintf ff "(PCSkip)"
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.path[@with path_component := Component.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
  let pp_roqc ff : t -> unit = fprintf ff "%a" (pp_roqc_list Component.pp_roqc)
end

module ConcreteMemory = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.concrete_memory]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | MemMM -> fprintf ff "MemMM"
    | MemGC -> fprintf ff "MemGC"
end

module Copyability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.copyability]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | NoCopy -> fprintf ff "NoCopy"
    | ExCopy -> fprintf ff "ExCopy"
    | ImCopy -> fprintf ff "ImCopy"
end

module Dropability = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.dropability]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | NoDrop -> fprintf ff "NoDrop"
    | ExDrop -> fprintf ff "ExDrop"
    | ImDrop -> fprintf ff "ImDrop"
end

module PrimitiveRep = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.primitive_rep]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | PtrR -> fprintf ff "PtrR"
    | I32R -> fprintf ff "I32R"
    | I64R -> fprintf ff "I64R"
    | F32R -> fprintf ff "F32R"
    | F64R -> fprintf ff "F64R"
end

module Sign = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.sign]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | SignU -> fprintf ff "SignU"
    | SignS -> fprintf ff "SignS"
end

module Float = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_type]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | F32T -> fprintf ff "F32T"
      | F64T -> fprintf ff "F64T"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_unop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | NegF -> fprintf ff "NegF"
      | AbsF -> fprintf ff "AbsF"
      | CeilF -> fprintf ff "CeilF"
      | FloorF -> fprintf ff "FloorF"
      | TruncF -> fprintf ff "TruncF"
      | NearestF -> fprintf ff "NearestF"
      | SqrtF -> fprintf ff "SqrtF"
  end

  module Binop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_binop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | AddF -> fprintf ff "AddF"
      | SubF -> fprintf ff "SubF"
      | MulF -> fprintf ff "MulF"
      | DivF -> fprintf ff "DivF"
      | MinF -> fprintf ff "MinF"
      | MaxF -> fprintf ff "MaxF"
      | CopySignF -> fprintf ff "CopySignF"
  end

  module Relop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.float_relop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | EqF -> fprintf ff "EqF"
      | NeF -> fprintf ff "NeF"
      | LtF -> fprintf ff "LtF"
      | GtF -> fprintf ff "GtF"
      | LeF -> fprintf ff "LeF"
      | GeF -> fprintf ff "GeF"
  end
end

module Int = struct
  module Type = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_type]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | I32T -> fprintf ff "I32T"
      | I64T -> fprintf ff "I64T"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_unop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | ClzI -> fprintf ff "ClzI"
      | CtzI -> fprintf ff "CtzI"
      | PopcntI -> fprintf ff "PopcntI"
  end

  module Binop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_binop[@with sign := Sign.t])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | AddI -> fprintf ff "AddI"
      | SubI -> fprintf ff "SubI"
      | MulI -> fprintf ff "MulI"
      | DivI sign -> fprintf ff "(DivI %a)" Sign.pp_roqc sign
      | RemI sign -> fprintf ff "(RemI %a)" Sign.pp_roqc sign
      | AndI -> fprintf ff "AndI"
      | OrI -> fprintf ff "OrI"
      | XorI -> fprintf ff "XorI"
      | ShlI -> fprintf ff "ShlI"
      | ShrI sign -> fprintf ff "(ShrI %a)" Sign.pp_roqc sign
      | RotlI -> fprintf ff "RotlI"
      | RotrI -> fprintf ff "RotrI"
  end

  module Relop = struct
    type t =
      [%import:
        (Richwasm_extract.RwSyntax.Core.int_relop[@with sign := Sign.t])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | EqI -> fprintf ff "EqI"
      | NeI -> fprintf ff "NeI"
      | LtI sign -> fprintf ff "(LtI %a)" Sign.pp_roqc sign
      | GtI sign -> fprintf ff "(GtI %a)" Sign.pp_roqc sign
      | LeI sign -> fprintf ff "(LeI %a)" Sign.pp_roqc sign
      | GeI sign -> fprintf ff "(GeI %a)" Sign.pp_roqc sign
  end

  module Testop = struct
    type t = [%import: Richwasm_extract.RwSyntax.Core.int_testop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff : t -> unit = function
      | EqzI -> fprintf ff "EqzI"
  end
end

module NumType = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.num_type
      [@with
        int_type := Int.Type.t;
        float_type := Float.Type.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | IntT it -> fprintf ff "(IntT %a)" Int.Type.pp_roqc it
    | FloatT ft -> fprintf ff "(FloatT %a)" Float.Type.pp_roqc ft
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
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | CWrap -> fprintf ff "CWrap"
    | CExtend sign -> fprintf ff "(CExtend %a)" Sign.pp_roqc sign
    | CTrunc (ft, it, sign) ->
        fprintf ff "(CTrunc %a %a %a)" Float.Type.pp_roqc ft Int.Type.pp_roqc it
          Sign.pp_roqc sign
    | CDemote -> fprintf ff "CDemote"
    | CPromote -> fprintf ff "CPromote"
    | CConvert (it, ft, sign) ->
        fprintf ff "(CConvert %a %a %a)" Int.Type.pp_roqc it Float.Type.pp_roqc
          ft Sign.pp_roqc sign
    | CReinterpret nt -> fprintf ff "(CReinterpret %a)" NumType.pp_roqc nt
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
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | IInt1 (t, o) ->
        fprintf ff "(IInt1 %a %a)" Int.Type.pp_roqc t Int.Unop.pp_roqc o
    | IInt2 (t, o) ->
        fprintf ff "(IInt2 %a %a)" Int.Type.pp_roqc t Int.Binop.pp_roqc o
    | IIntTest (t, o) ->
        fprintf ff "(IIntTest %a %a)" Int.Type.pp_roqc t Int.Testop.pp_roqc o
    | IIntRel (t, o) ->
        fprintf ff "(IIntRel %a %a)" Int.Type.pp_roqc t Int.Relop.pp_roqc o
    | IFloat1 (t, o) ->
        fprintf ff "(IFloat1 %a %a)" Float.Type.pp_roqc t Float.Unop.pp_roqc o
    | IFloat2 (t, o) ->
        fprintf ff "(IFloat2 %a %a)" Float.Type.pp_roqc t Float.Binop.pp_roqc o
    | IFloatRel (t, o) ->
        fprintf ff "(IFloatRel %a %a)" Float.Type.pp_roqc t Float.Relop.pp_roqc
          o
    | ICvt o -> fprintf ff "(ICvt %a)" ConversionOp.pp_roqc o
end

module Representation = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.representation
      [@with
        primitive_rep := PrimitiveRep.t;
        Z.t := Z'.t])]
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_representation
  let ren = Richwasm_extract.RwSyntax.Core.ren_representation
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  (* HACK: can't get @@deriving variants to work with ppx_import *)
  let varR x = VarR x

  let rec pp_roqc ff : t -> unit = function
    | VarR x -> fprintf ff "(VarR %a)" Z.pp_print x
    | SumR rs -> fprintf ff "(SumR %a)" (pp_roqc_list pp_roqc) rs
    | ProdR rs -> fprintf ff "(ProdR %a)" (pp_roqc_list pp_roqc) rs
    | PrimR p -> fprintf ff "(PrimR %a)" PrimitiveRep.pp_roqc p
end

module Size = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.size
      [@with
        representation := Representation.t;
        Z.t := Z'.t])]
  [@@deriving eq, ord, sexp]

  (* HACK: can't get @@deriving variants to work with ppx_import *)
  let varS x = VarS x
  let subst = Richwasm_extract.RwSyntax.Core.subst_size
  let ren = Richwasm_extract.RwSyntax.Core.ren_size
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp_roqc ff : t -> unit = function
    | VarS x -> fprintf ff "(VarS %a)" Z.pp_print x
    | SumS ss -> fprintf ff "(SumS %a)" (pp_roqc_list pp_roqc) ss
    | ProdS ss -> fprintf ff "(ProdS %a)" (pp_roqc_list pp_roqc) ss
    | RepS rep -> fprintf ff "(RepS %a)" Representation.pp_roqc rep
    | ConstS i -> fprintf ff "(ConstS %a)" Z.pp_print i
end

module Sizity = struct
  type t =
    [%import: (Richwasm_extract.RwSyntax.Core.sizity[@with size := Size.t])]
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_sizity
  let ren = Richwasm_extract.RwSyntax.Core.ren_sizity
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | Sized size -> fprintf ff "(Sized %a)" Size.pp_roqc size
    | Unsized -> fprintf ff "Unsized"
end

module Memory = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.memory
      [@with
        concrete_memory := ConcreteMemory.t;
        Z.t := Z'.t])]
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_memory
  let ren = Richwasm_extract.RwSyntax.Core.ren_memory
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  (* HACK: can't get @@deriving variants to work with ppx_import *)
  let varM x = VarM x

  let pp_roqc ff : t -> unit = function
    | VarM x -> fprintf ff "(VarM %a)" Z.pp_print x
    | ConstM concrete ->
        fprintf ff "(ConstM %a)" ConcreteMemory.pp_roqc concrete
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
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_kind
  let ren = Richwasm_extract.RwSyntax.Core.ren_kind
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | VALTYPE (rep, copy, drop) ->
        fprintf ff "(VALTYPE %a %a %a)" Representation.pp_roqc rep
          Copyability.pp_roqc copy Dropability.pp_roqc drop
    | MEMTYPE (sizity, mem, drop) ->
        fprintf ff "(MEMTYPE %a %a %a)" Sizity.pp_roqc sizity Memory.pp_roqc mem
          Dropability.pp_roqc drop
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
          function_type := function_typ;
          Z.t := Z'.t])]

    and function_typ =
      [%import:
        (Richwasm_extract.RwSyntax.Core.function_type
        [@with
          kind := Kind.t;
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving eq, ord, sexp]

    let pp_sexp_typ ff x = Sexp.pp_hum ff (sexp_of_typ x)
    let pp_sexp_function_typ ff x = Sexp.pp_hum ff (sexp_of_function_typ x)

    let rec pp_roqc_typ ff : typ -> unit = function
      | VarT x -> fprintf ff "(VarT %a)" Z.pp_print x
      | I31T kind -> fprintf ff "(I31T %a)" Kind.pp_roqc kind
      | NumT (kind, nt) ->
          fprintf ff "(NumT %a %a)" Kind.pp_roqc kind NumType.pp_roqc nt
      | SumT (kind, ts) ->
          fprintf ff "(SumT %a %a)" Kind.pp_roqc kind (pp_roqc_list pp_roqc_typ)
            ts
      | VariantT (kind, ts) ->
          fprintf ff "(VariantT %a %a)" Kind.pp_roqc kind
            (pp_roqc_list pp_roqc_typ) ts
      | ProdT (kind, ts) ->
          fprintf ff "(ProdT %a %a)" Kind.pp_roqc kind
            (pp_roqc_list pp_roqc_typ) ts
      | StructT (kind, ts) ->
          fprintf ff "(ProdT %a %a)" Kind.pp_roqc kind
            (pp_roqc_list pp_roqc_typ) ts
      | RefT (kind, mem, t) ->
          fprintf ff "(RefT %a %a %a)" Kind.pp_roqc kind Memory.pp_roqc mem
            pp_roqc_typ t
      | GCPtrT (kind, t) ->
          fprintf ff "(GCPtrT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | CodeRefT (kind, ft) ->
          fprintf ff "(CodeRefT %a %a)" Kind.pp_roqc kind pp_roqc_function_typ
            ft
      | PadT (kind, size, t) ->
          fprintf ff "(PadT %a %a %a)" Kind.pp_roqc kind Size.pp_roqc size
            pp_roqc_typ t
      | SerT (kind, t) ->
          fprintf ff "(SerT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | RecT (kind, t) ->
          fprintf ff "(RecT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | ExistsMemT (kind, t) ->
          fprintf ff "(ExistsMemT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | ExistsRepT (kind, t) ->
          fprintf ff "(ExistsRepT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | ExistsSizeT (kind, t) ->
          fprintf ff "(ExistsSizeT %a %a)" Kind.pp_roqc kind pp_roqc_typ t
      | ExistsTypeT (k1, k2, t) ->
          fprintf ff "(ExistsTypeT %a %a %a)" Kind.pp_roqc k1 Kind.pp_roqc k2
            pp_roqc_typ t

    and pp_roqc_function_typ ff : function_typ -> unit = function
      | MonoFunT (t1s, t2s) ->
          fprintf ff "(MonoFunT %a %a)" (pp_roqc_list pp_roqc_typ) t1s
            (pp_roqc_list pp_roqc_typ) t2s
      | ForallMemT ft -> fprintf ff "(ForallMemT %a)" pp_roqc_function_typ ft
      | ForallRepT ft -> fprintf ff "(ForallRepT %a)" pp_roqc_function_typ ft
      | ForallSizeT ft -> fprintf ff "(ForallSizeT %a)" pp_roqc_function_typ ft
      | ForallTypeT (kind, ft) ->
          fprintf ff "(ForallTypeT %a %a)" Kind.pp_roqc kind
            pp_roqc_function_typ ft
  end
end

module Type = struct
  include Internal.Types

  type t = Internal.Types.typ [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_type
  let ren = Richwasm_extract.RwSyntax.Core.ren_type

  (* HACK: can't get @@deriving variants to work with ppx_import *)
  let varT x = VarT x
  let pp_sexp = Internal.Types.pp_sexp_typ
  let pp_roqc = Internal.Types.pp_roqc_typ
end

module FunctionType = struct
  include Internal.Types

  type t = Internal.Types.function_typ [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_function_type
  let ren = Richwasm_extract.RwSyntax.Core.ren_function_type
  let pp_sexp = Internal.Types.pp_sexp_function_typ
  let pp_roqc = Internal.Types.pp_roqc_function_typ
end

module InstructionType = struct
  type t =
    [%import:
      (Richwasm_extract.RwSyntax.Core.instruction_type
      [@with coq_type := Type.t])]
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_function_type
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | InstrT (t_in, t_out) ->
        fprintf ff "(InstrT %a %a)"
          (pp_roqc_list Type.pp_roqc)
          t_in
          (pp_roqc_list Type.pp_roqc)
          t_out
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
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff : t -> unit = function
    | MemI mem -> fprintf ff "(MemI %a)" Memory.pp_roqc mem
    | RepI rep -> fprintf ff "(RepI %a)" Representation.pp_roqc rep
    | SizeI size -> fprintf ff "(SizeI %a)" Size.pp_roqc size
    | TypeI typ -> fprintf ff "(TypeI %a)" Type.pp_roqc typ
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
        path := Path.t;
        Z.t := Z'.t])]
  [@@deriving eq, ord, sexp]

  let subst = Richwasm_extract.RwSyntax.Core.subst_instruction
  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp_roqc ff : t -> unit =
    let pp_it = InstructionType.pp_roqc in
    let pp_lfx = pp_print_list (pp_roqc_option Type.pp_roqc) in
    let pp_instrs = pp_roqc_list pp_roqc in
    function
    | INop it -> fprintf ff "(INop %a)" pp_it it
    | IUnreachable it -> fprintf ff "(IUnreachable %a)" pp_it it
    | ICopy it -> fprintf ff "(ICopy %a)" pp_it it
    | IDrop it -> fprintf ff "(IDrop %a)" pp_it it
    | INum (it, ni) ->
        fprintf ff "(INum %a %a)" pp_it it NumInstruction.pp_roqc ni
    | INumConst (it, i) -> fprintf ff "(INumConst %a %a)" pp_it it Z.pp_print i
    | IBlock (it, lfx, instrs) ->
        fprintf ff "(IBlock %a %a %a)" pp_it it pp_lfx lfx pp_instrs instrs
    | ILoop (it, instrs) -> fprintf ff "(ILoop %a %a)" pp_it it pp_instrs instrs
    | IIte (it, lfx, e_thn, e_els) ->
        fprintf ff "(IIte %a %a %a %a)" pp_it it pp_lfx lfx pp_instrs e_thn
          pp_instrs e_els
    | IBr (it, i) -> fprintf ff "(IBr %a %a)" pp_it it Z.pp_print i
    | IReturn it -> fprintf ff "(IReturn %a)" pp_it it
    | ILocalGet (it, i) -> fprintf ff "(ILocalGet %a %a)" pp_it it Z.pp_print i
    | ILocalSet (it, i) -> fprintf ff "(ILocalSet %a %a)" pp_it it Z.pp_print i
    | ICodeRef (it, i) -> fprintf ff "(ICodeRef %a %a)" pp_it it Z.pp_print i
    | IInst (it, idx) -> fprintf ff "(IInst %a %a)" pp_it it Index.pp_roqc idx
    | ICall (it, i, idxs) ->
        fprintf ff "(ICall %a %a %a)" pp_it it Z.pp_print i
          (pp_roqc_list Index.pp_roqc)
          idxs
    | ICallIndirect it -> fprintf ff "(ICallIndirect %a)" pp_it it
    | IInject (it, i) -> fprintf ff "(IInject %a %a)" pp_it it Z.pp_print i
    | ICase (it, lfx, cases) ->
        fprintf ff "(ICase %a %a %a)" pp_it it pp_lfx lfx
          (pp_roqc_list pp_instrs) cases
    | IGroup it -> fprintf ff "(IGroup %a)" pp_it it
    | IUngroup it -> fprintf ff "(IUngroup %a)" pp_it it
    | IFold it -> fprintf ff "(IFold %a)" pp_it it
    | IUnfold it -> fprintf ff "(IUnfold %a)" pp_it it
    | IPack it -> fprintf ff "(IPack %a)" pp_it it
    | IUnpack (it, lfx, instrs) ->
        fprintf ff "(IUnpack %a %a %a)" pp_it it pp_lfx lfx pp_instrs instrs
    | ITag it -> fprintf ff "(ITag %a)" pp_it it
    | IUntag it -> fprintf ff "(IUntag %a)" pp_it it
    | INew it -> fprintf ff "(INew %a)" pp_it it
    | ILoad (it, p) -> fprintf ff "(ILoad  %a %a)" pp_it it Path.pp_roqc p
    | IStore (it, p) -> fprintf ff "(IStore  %a %a)" pp_it it Path.pp_roqc p
    | ISwap (it, p) -> fprintf ff "(ISwap  %a %a)" pp_it it Path.pp_roqc p
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
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_roqc ff ({ mf_type; mf_locals; mf_body } : t) : unit =
      fprintf ff "@[<v 0>{|@[<hv 2>@,";
      fprintf ff "@[<2>mf_type :=@ %a;@]@ " FunctionType.pp_roqc mf_type;
      fprintf ff "@[<2>mf_locals :=@ %a;@]@ "
        (pp_roqc_list Representation.pp_roqc)
        mf_locals;
      fprintf ff "@[<2>mf_body :=@ %a@];@,"
        (pp_roqc_list Instruction.pp_roqc)
        mf_body;
      fprintf ff "@]|}@]"
  end

  type t =
    [%import:
      (Richwasm_extract.RwSyntax.module0
      [@with
        Core.function_type := FunctionType.t;
        module_function := Function.t;
        Z.t := Z'.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_roqc ff ({ m_imports; m_functions; m_table; m_exports } : t) : unit =
    fprintf ff "@[<v 0>{|@[<hv 2>@,";
    fprintf ff "@[<2>m_imports :=@ %a;@]@ "
      (pp_roqc_list FunctionType.pp_roqc)
      m_imports;
    fprintf ff "@[<2>m_functions :=@ %a;@]@ "
      (pp_roqc_list Function.pp_roqc)
      m_functions;
    fprintf ff "@[<2>m_table :=@ %a;@]@ " (pp_roqc_list Z.pp_print) m_table;
    fprintf ff "@[<2>m_exports :=@ %a;@]@," (pp_roqc_list Z.pp_print) m_exports;
    fprintf ff "@]|}@]"
end
