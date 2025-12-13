open! Base
open! Stdlib.Format
open Util

let pp_rocq_list (pp : formatter -> 'a -> unit) ff (lst : 'a list) =
  fprintf ff "@[<v 0>@[<hv 2>@<0>[";
  if not (List.is_empty lst) then fprintf ff "@<0> ";
  List.iteri
    ~f:(fun i x ->
      if i <> 0 then fprintf ff ";@ ";
      fprintf ff "@[<2>%a@]" pp x)
    lst;
  fprintf ff "@]]@]"

let pp_rocq_option (pp : formatter -> 'a -> unit) ff = function
  | Some x -> fprintf ff "@[<2>(Some@ %a)@]" pp x
  | None -> fprintf ff "None"

module Big_int_Z' = struct
  include Big_int_Z

  let equal_big_int = eq_big_int
  let sexp_of_big_int (z : big_int) = Sexp.Atom (Z.to_string z)

  let big_int_of_sexp : Sexp.t -> big_int = function
    | Sexp.Atom s -> Z.of_string s
    | _ -> failwith "expected atom"
end

module BaseMemory = struct
  type t = [%import: Richwasm_extract.Rw.Core.base_memory]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | MemMM -> fprintf ff "MemMM"
    | MemGC -> fprintf ff "MemGC"

  let pp ff : t -> _ = function
    | MemMM -> fprintf ff "mm"
    | MemGC -> fprintf ff "gc"
end

module Copyability = struct
  type t = [%import: Richwasm_extract.Rw.Core.copyability]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | NoCopy -> fprintf ff "NoCopy"
    | ExCopy -> fprintf ff "ExCopy"
    | ImCopy -> fprintf ff "ImCopy"

  let pp ff : t -> _ = function
    | NoCopy -> fprintf ff "nocopy"
    | ExCopy -> fprintf ff "excopy"
    | ImCopy -> fprintf ff "imcopy"

  let le a b =
    match (a, b) with
    | ImCopy, _ -> true
    | ExCopy, (ExCopy | NoCopy) -> true
    | NoCopy, NoCopy -> true
    | _ -> false

  let meet a b =
    match (a, b) with
    | NoCopy, _ | _, NoCopy -> NoCopy
    | ExCopy, _ | _, ExCopy -> ExCopy
    | ImCopy, ImCopy -> ImCopy
end

module Dropability = struct
  type t = [%import: Richwasm_extract.Rw.Core.dropability]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | ExDrop -> fprintf ff "ExDrop"
    | ImDrop -> fprintf ff "ImDrop"

  let pp ff : t -> _ = function
    | ExDrop -> fprintf ff "exdrop"
    | ImDrop -> fprintf ff "imdrop"

  let le a b =
    match (a, b) with
    | ImDrop, _ -> true
    | ExDrop, ExDrop -> true
    | _ -> false

  let meet a b =
    match (a, b) with
    | ExDrop, _ | _, ExDrop -> ExDrop
    | ImDrop, ImDrop -> ImDrop
end

module AtomicRep = struct
  type t = [%import: Richwasm_extract.Rw.Core.atomic_rep]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | PtrR -> fprintf ff "PtrR"
    | I32R -> fprintf ff "I32R"
    | I64R -> fprintf ff "I64R"
    | F32R -> fprintf ff "F32R"
    | F64R -> fprintf ff "F64R"

  let pp ff = function
    | PtrR -> fprintf ff "ptr"
    | I32R -> fprintf ff "i32"
    | I64R -> fprintf ff "i64"
    | F32R -> fprintf ff "f32"
    | F64R -> fprintf ff "f64"
end

module Sign = struct
  type t = [%import: Richwasm_extract.Rw.Core.sign] [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | SignU -> fprintf ff "SignU"
    | SignS -> fprintf ff "SignS"

  let pp ff : t -> _ = function
    | SignU -> fprintf ff "u"
    | SignS -> fprintf ff "s"
end

module Float = struct
  module Type = struct
    type t = [%import: Richwasm_extract.Rw.Core.float_type]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | F32T -> fprintf ff "F32T"
      | F64T -> fprintf ff "F64T"

    let pp ff : t -> _ = function
      | F32T -> fprintf ff "f32"
      | F64T -> fprintf ff "f64"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.Rw.Core.float_unop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | NegF -> fprintf ff "NegF"
      | AbsF -> fprintf ff "AbsF"
      | CeilF -> fprintf ff "CeilF"
      | FloorF -> fprintf ff "FloorF"
      | TruncF -> fprintf ff "TruncF"
      | NearestF -> fprintf ff "NearestF"
      | SqrtF -> fprintf ff "SqrtF"

    let pp ff : t -> _ = function
      | NegF -> fprintf ff "neg"
      | AbsF -> fprintf ff "abs"
      | CeilF -> fprintf ff "ceil"
      | FloorF -> fprintf ff "floor"
      | TruncF -> fprintf ff "trunc"
      | NearestF -> fprintf ff "nearest"
      | SqrtF -> fprintf ff "sqrt"
  end

  module Binop = struct
    type t = [%import: Richwasm_extract.Rw.Core.float_binop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | AddF -> fprintf ff "AddF"
      | SubF -> fprintf ff "SubF"
      | MulF -> fprintf ff "MulF"
      | DivF -> fprintf ff "DivF"
      | MinF -> fprintf ff "MinF"
      | MaxF -> fprintf ff "MaxF"
      | CopySignF -> fprintf ff "CopySignF"

    let pp ff : t -> _ = function
      | AddF -> fprintf ff "add"
      | SubF -> fprintf ff "sub"
      | MulF -> fprintf ff "mul"
      | DivF -> fprintf ff "div"
      | MinF -> fprintf ff "min"
      | MaxF -> fprintf ff "max"
      | CopySignF -> fprintf ff "copysign"
  end

  module Relop = struct
    type t = [%import: Richwasm_extract.Rw.Core.float_relop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | EqF -> fprintf ff "EqF"
      | NeF -> fprintf ff "NeF"
      | LtF -> fprintf ff "LtF"
      | GtF -> fprintf ff "GtF"
      | LeF -> fprintf ff "LeF"
      | GeF -> fprintf ff "GeF"

    let pp ff : t -> _ = function
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
    type t = [%import: Richwasm_extract.Rw.Core.int_type]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | I32T -> fprintf ff "I32T"
      | I64T -> fprintf ff "I64T"

    let pp ff : t -> _ = function
      | I32T -> fprintf ff "i32"
      | I64T -> fprintf ff "i64"
  end

  module Unop = struct
    type t = [%import: Richwasm_extract.Rw.Core.int_unop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | ClzI -> fprintf ff "ClzI"
      | CtzI -> fprintf ff "CtzI"
      | PopcntI -> fprintf ff "PopcntI"

    let pp ff : t -> _ = function
      | ClzI -> fprintf ff "clz"
      | CtzI -> fprintf ff "ctz"
      | PopcntI -> fprintf ff "popcnt"
  end

  module Binop = struct
    type t =
      [%import: (Richwasm_extract.Rw.Core.int_binop[@with sign := Sign.t])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | AddI -> fprintf ff "AddI"
      | SubI -> fprintf ff "SubI"
      | MulI -> fprintf ff "MulI"
      | DivI sign -> fprintf ff "@[<2>(DivI@ %a)@]" Sign.pp_rocq sign
      | RemI sign -> fprintf ff "@[<2>(RemI@ %a)@]" Sign.pp_rocq sign
      | AndI -> fprintf ff "AndI"
      | OrI -> fprintf ff "OrI"
      | XorI -> fprintf ff "XorI"
      | ShlI -> fprintf ff "ShlI"
      | ShrI sign -> fprintf ff "@[<2>(ShrI@ %a)@]" Sign.pp_rocq sign
      | RotlI -> fprintf ff "RotlI"
      | RotrI -> fprintf ff "RotrI"

    let pp ff : t -> _ = function
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
      [%import: (Richwasm_extract.Rw.Core.int_relop[@with sign := Sign.t])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | EqI -> fprintf ff "EqI"
      | NeI -> fprintf ff "NeI"
      | LtI sign -> fprintf ff "@[<2>(LtI@ %a)@]" Sign.pp_rocq sign
      | GtI sign -> fprintf ff "@[<2>(GtI@ %a)@]" Sign.pp_rocq sign
      | LeI sign -> fprintf ff "@[<2>(LeI@ %a)@]" Sign.pp_rocq sign
      | GeI sign -> fprintf ff "@[<2>(GeI@ %a)@]" Sign.pp_rocq sign

    let pp ff : t -> _ = function
      | EqI -> fprintf ff "eq"
      | NeI -> fprintf ff "ne"
      | LtI s -> fprintf ff "lt_%a" Sign.pp s
      | GtI s -> fprintf ff "gt_%a" Sign.pp s
      | LeI s -> fprintf ff "le_%a" Sign.pp s
      | GeI s -> fprintf ff "ge_%a" Sign.pp s
  end

  module Testop = struct
    type t = [%import: Richwasm_extract.Rw.Core.int_testop]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff : t -> _ = function
      | EqzI -> fprintf ff "EqzI"

    let pp ff : t -> _ = function
      | EqzI -> fprintf ff "eqz"
  end
end

module NumType = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.num_type
      [@with
        int_type := Int.Type.t;
        float_type := Float.Type.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | IntT it -> fprintf ff "@[<2>(IntT@ %a)@]" Int.Type.pp_rocq it
    | FloatT ft -> fprintf ff "@[<2>(FloatT@ %a)@]" Float.Type.pp_rocq ft

  let pp ff : t -> _ = function
    | IntT it -> Int.Type.pp ff it
    | FloatT ft -> Float.Type.pp ff ft
end

module ConversionOp = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.conversion_op
      [@with
        sign := Sign.t;
        int_type := Int.Type.t;
        float_type := Float.Type.t;
        num_type := NumType.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | CWrap -> fprintf ff "CWrap"
    | CExtend sign -> fprintf ff "@[<2>(CExtend@ %a)@]" Sign.pp_rocq sign
    | CTrunc (ft, it, sign) ->
        fprintf ff "@[<2>(CTrunc@ %a@ %a@ %a)@]" Float.Type.pp_rocq ft
          Int.Type.pp_rocq it Sign.pp_rocq sign
    | CDemote -> fprintf ff "CDemote"
    | CPromote -> fprintf ff "CPromote"
    | CConvert (it, ft, sign) ->
        fprintf ff "@[<2>(CConvert@ %a@ %a@ %a)@]" Int.Type.pp_rocq it
          Float.Type.pp_rocq ft Sign.pp_rocq sign
    | CReinterpret nt ->
        fprintf ff "@[<2>(CReinterpret@ %a)@]" NumType.pp_rocq nt

  let pp ff : t -> _ = function
    | CWrap -> fprintf ff "i32.wrap_i64"
    | CExtend s -> fprintf ff "i64.extend_i32_%a" Sign.pp s
    | CTrunc (ft, it, sign) ->
        fprintf ff "%a.trunc_%a_%a" Int.Type.pp it Float.Type.pp ft Sign.pp sign
    | CDemote -> fprintf ff "f32.demote_f64"
    | CPromote -> fprintf ff "f64.promote_f32"
    | CConvert (it, ft, sign) ->
        fprintf ff "%a.convert_%a_%a" Float.Type.pp ft Int.Type.pp it Sign.pp
          sign
    | CReinterpret (IntT I32T) -> fprintf ff "f32.reinterpret_i32"
    | CReinterpret (IntT I64T) -> fprintf ff "f64.reinterpret_i64"
    | CReinterpret (FloatT F32T) -> fprintf ff "i32.reinterpret_f32"
    | CReinterpret (FloatT F64T) -> fprintf ff "i64.reinterpret_f64"
end

module NumInstruction = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.num_instruction
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

  let pp_rocq ff : t -> _ = function
    | IInt1 (t, o) ->
        fprintf ff "@[<2>(IInt1@ %a@ %a)@]" Int.Type.pp_rocq t Int.Unop.pp_rocq
          o
    | IInt2 (t, o) ->
        fprintf ff "@[<2>(IInt2@ %a@ %a)@]" Int.Type.pp_rocq t Int.Binop.pp_rocq
          o
    | IIntTest (t, o) ->
        fprintf ff "@[<2>(IIntTest@ %a@ %a)@]" Int.Type.pp_rocq t
          Int.Testop.pp_rocq o
    | IIntRel (t, o) ->
        fprintf ff "@[<2>(IIntRel@ %a@ %a)@]" Int.Type.pp_rocq t
          Int.Relop.pp_rocq o
    | IFloat1 (t, o) ->
        fprintf ff "@[<2>(IFloat1@ %a@ %a)@]" Float.Type.pp_rocq t
          Float.Unop.pp_rocq o
    | IFloat2 (t, o) ->
        fprintf ff "@[<2>(IFloat2@ %a@ %a)@]" Float.Type.pp_rocq t
          Float.Binop.pp_rocq o
    | IFloatRel (t, o) ->
        fprintf ff "@[<2>(IFloatRel@ %a@ %a)@]" Float.Type.pp_rocq t
          Float.Relop.pp_rocq o
    | ICvt o -> fprintf ff "@[<2>(ICvt@ %a)@]" ConversionOp.pp_rocq o

  let pp ff : t -> _ = function
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
      (Richwasm_extract.Rw.Core.representation
      [@with
        atomic_rep := AtomicRep.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp_rocq ff : t -> _ = function
    | VarR x -> fprintf ff "@[<2>(VarR@ %a)@]" Z.pp_print x
    | SumR rs -> fprintf ff "@[<2>(SumR@ %a)@]" (pp_rocq_list pp_rocq) rs
    | ProdR rs -> fprintf ff "@[<2>(ProdR@ %a)@]" (pp_rocq_list pp_rocq) rs
    | AtomR a -> fprintf ff "@[<2>(AtomR@ %a)@]" AtomicRep.pp_rocq a

  let rec pp ff = function
    | VarR x -> fprintf ff "@[<2>(var %a)@]" Z.pp_print x
    | SumR rs -> fprintf ff "@[<2>(sum%a)@]" (pp_print_list_pre_space pp) rs
    | ProdR rs -> fprintf ff "@[<2>(prod%a)@]" (pp_print_list_pre_space pp) rs
    | AtomR prim -> AtomicRep.pp ff prim

  let subst = Richwasm_extract.Rw.Core.subst_representation
  let ren = Richwasm_extract.Rw.Core.ren_representation
end

module Size = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.size
      [@with
        representation := Representation.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp_rocq ff : t -> _ = function
    | VarS x -> fprintf ff "@[<2>(VarS@ %a)@]" Z.pp_print x
    | SumS ss -> fprintf ff "@[<2>(SumS@ %a)@]" (pp_rocq_list pp_rocq) ss
    | ProdS ss -> fprintf ff "@[<2>(ProdS@ %a)@]" (pp_rocq_list pp_rocq) ss
    | RepS rep -> fprintf ff "@[<2>(RepS@ %a)@]" Representation.pp_rocq rep
    | ConstS i -> fprintf ff "@[<2>(ConstS@ %a)@]" Z.pp_print i

  let rec pp ff = function
    | VarS x -> fprintf ff "@[<2>(var %a)@]" Z.pp_print x
    | SumS rs -> fprintf ff "@[<2>(sum%a)@]" (pp_print_list_pre_space pp) rs
    | ProdS rs -> fprintf ff "@[<2>(prod%a)@]" (pp_print_list_pre_space pp) rs
    | RepS r -> fprintf ff "@[<2>(rep %a)@]" Representation.pp r
    | ConstS prim -> fprintf ff "@[<2>(const %a)@]" Z.pp_print prim

  let subst = Richwasm_extract.Rw.Core.subst_size
  let ren = Richwasm_extract.Rw.Core.ren_size
end

module Memory = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.memory
      [@with
        base_memory := BaseMemory.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | VarM x -> fprintf ff "@[<2>(VarM@ %a)@]" Z.pp_print x
    | BaseM bm -> fprintf ff "@[<2>(BaseM@ %a)@]" BaseMemory.pp_rocq bm

  let pp ff : t -> _ = function
    | VarM i -> fprintf ff "@[<2>(var %a)@]" Z.pp_print i
    | BaseM m -> fprintf ff "@[<2>(base %a)@]" BaseMemory.pp m

  let subst = Richwasm_extract.Rw.Core.subst_memory
  let ren = Richwasm_extract.Rw.Core.ren_memory
end

module Kind = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.kind
      [@with
        representation := Representation.t;
        copyability := Copyability.t;
        dropability := Dropability.t;
        size := Size.t;
        memory := Memory.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | VALTYPE (rep, copy, drop) ->
        fprintf ff "@[<2>(VALTYPE@ %a@ %a@ %a)@]" Representation.pp_rocq rep
          Copyability.pp_rocq copy Dropability.pp_rocq drop
    | MEMTYPE (size, drop) ->
        fprintf ff "@[<2>(MEMTYPE@ %a@ %a)@]" Size.pp_rocq size
          Dropability.pp_rocq drop

  let pp ff = function
    | VALTYPE (r, c, d) ->
        fprintf ff "@[<2>(val@ %a@ %a@ %a)@]" Representation.pp r Copyability.pp
          c Dropability.pp d
    | MEMTYPE (s, d) ->
        fprintf ff "@[<2>(mem@ %a@ %a)@]" Size.pp s Dropability.pp d

  let subst = Richwasm_extract.Rw.Core.subst_kind
  let ren = Richwasm_extract.Rw.Core.ren_kind
end

(* work around bug? with ppx_import *)
module Internal = struct
  module Types = struct
    type typ =
      [%import:
        (Richwasm_extract.Rw.Core.coq_type
        [@with
          kind := Kind.t;
          num_type := NumType.t;
          memory := Memory.t;
          representation := Representation.t;
          size := Size.t;
          coq_type := typ;
          function_type := function_typ;
          Big_int_Z.big_int := Big_int_Z'.big_int])]

    and function_typ =
      [%import:
        (Richwasm_extract.Rw.Core.function_type
        [@with
          kind := Kind.t;
          coq_type := typ;
          function_type := function_typ])]
    [@@deriving eq, ord, sexp]

    let pp_sexp_typ ff x = Sexp.pp_hum ff (sexp_of_typ x)
    let pp_sexp_function_typ ff x = Sexp.pp_hum ff (sexp_of_function_typ x)

    let rec pp_rocq_typ ff : typ -> unit = function
      | VarT x -> fprintf ff "@[<2>(VarT@ %a)@]" Z.pp_print x
      | I31T kind -> fprintf ff "@[<2>(I31T@ %a)@]" Kind.pp_rocq kind
      | NumT (kind, nt) ->
          fprintf ff "@[<2>(NumT@ %a@ %a)@]" Kind.pp_rocq kind NumType.pp_rocq
            nt
      | SumT (kind, ts) ->
          fprintf ff "@[<2>(SumT@ %a@ %a)@]" Kind.pp_rocq kind
            (pp_rocq_list pp_rocq_typ) ts
      | VariantT (kind, ts) ->
          fprintf ff "@[<2>(VariantT@ %a@ %a)@]" Kind.pp_rocq kind
            (pp_rocq_list pp_rocq_typ) ts
      | ProdT (kind, ts) ->
          fprintf ff "@[<2>(ProdT@ %a@ %a)@]" Kind.pp_rocq kind
            (pp_rocq_list pp_rocq_typ) ts
      | StructT (kind, ts) ->
          fprintf ff "@[<2>(ProdT@ %a@ %a)@]" Kind.pp_rocq kind
            (pp_rocq_list pp_rocq_typ) ts
      | RefT (kind, mem, t) ->
          fprintf ff "@[<2>(RefT@ %a@ %a@ %a)@]" Kind.pp_rocq kind
            Memory.pp_rocq mem pp_rocq_typ t
      | CodeRefT (kind, ft) ->
          fprintf ff "@[<2>(CodeRefT@ %a@ %a)@]" Kind.pp_rocq kind
            pp_rocq_function_typ ft
      | SerT (kind, t) ->
          fprintf ff "@[<2>(SerT@ %a@ %a)@]" Kind.pp_rocq kind pp_rocq_typ t
      | PlugT (kind, rep) ->
          fprintf ff "@[<2>(PlugT@ %a@ %a)@]" Kind.pp_rocq kind
            Representation.pp_rocq rep
      | SpanT (kind, size) ->
          fprintf ff "@[<2>(SpanT@ %a@ %a)@]" Kind.pp_rocq kind Size.pp_rocq
            size
      | RecT (kind, t) ->
          fprintf ff "@[<2>(RecT@ %a@ %a)@]" Kind.pp_rocq kind pp_rocq_typ t
      | ExistsMemT (kind, t) ->
          fprintf ff "@[<2>(ExistsMemT@ %a@ %a)@]" Kind.pp_rocq kind pp_rocq_typ
            t
      | ExistsRepT (kind, t) ->
          fprintf ff "@[<2>(ExistsRepT@ %a@ %a)@]" Kind.pp_rocq kind pp_rocq_typ
            t
      | ExistsSizeT (kind, t) ->
          fprintf ff "@[<2>(ExistsSizeT@ %a@ %a)@]" Kind.pp_rocq kind
            pp_rocq_typ t
      | ExistsTypeT (k1, k2, t) ->
          fprintf ff "@[<2>(ExistsTypeT@ %a@ %a@ %a)@]" Kind.pp_rocq k1
            Kind.pp_rocq k2 pp_rocq_typ t

    and pp_rocq_function_typ ff : function_typ -> unit = function
      | MonoFunT (t1s, t2s) ->
          fprintf ff "@[<2>(MonoFunT@ %a@ %a)@]" (pp_rocq_list pp_rocq_typ) t1s
            (pp_rocq_list pp_rocq_typ) t2s
      | ForallMemT ft ->
          fprintf ff "@[<2>(ForallMemT@ %a)@]" pp_rocq_function_typ ft
      | ForallRepT ft ->
          fprintf ff "@[<2>(ForallRepT@ %a)@]" pp_rocq_function_typ ft
      | ForallSizeT ft ->
          fprintf ff "@[<2>(ForallSizeT@ %a)@]" pp_rocq_function_typ ft
      | ForallTypeT (kind, ft) ->
          fprintf ff "@[<2>(ForallTypeT@ %a@ %a)@]" Kind.pp_rocq kind
            pp_rocq_function_typ ft

    let rec pp_typ ff : typ -> unit = function
      | VarT i -> fprintf ff "@[<2>(var@ %a)@]" Z.pp_print i
      | I31T k -> fprintf ff "@[<2>(i31@ %a)@]" Kind.pp k
      | NumT (k, nt) ->
          fprintf ff "@[<2>(num@ %a@ %a)@]" Kind.pp k NumType.pp nt
      | SumT (k, ts) ->
          fprintf ff "@[<2>(sum@ %a@ %a)@]" Kind.pp k
            (pp_print_list_pre_space pp_typ)
            ts
      | VariantT (k, ts) ->
          fprintf ff "@[<2>(variant@ %a%a)@]" Kind.pp k
            (pp_print_list_pre_space pp_typ)
            ts
      | ProdT (k, ts) ->
          fprintf ff "@[<2>(prod@ %a%a)@]" Kind.pp k
            (pp_print_list_pre_space pp_typ)
            ts
      | StructT (k, ts) ->
          fprintf ff "@[<2>(struct@ %a%a)@]" Kind.pp k
            (pp_print_list_pre_space pp_typ)
            ts
      | RefT (k, m, t) ->
          fprintf ff "@[<2>(ref@ %a@ %a@ %a)@]" Kind.pp k Memory.pp m pp_typ t
      | CodeRefT (k, ft) ->
          fprintf ff "@[<2>(coderef@ %a@ %a)@]" Kind.pp k pp_function_typ ft
      | SerT (k, t) -> fprintf ff "@[<2>(ser@ %a@ %a)@]" Kind.pp k pp_typ t
      | PlugT (k, r) ->
          fprintf ff "@[<2>(plug@ %a@ %a)@]" Kind.pp k Representation.pp r
      | SpanT (k, s) -> fprintf ff "@[<2>(span@ %a@ %a)@]" Kind.pp k Size.pp s
      | RecT (kind, t) ->
          fprintf ff "@[<2>(rec@ %a@ %a)@]" Kind.pp kind pp_typ t
      | ExistsMemT (kind, t) ->
          fprintf ff "@[<2>(exists.mem@ %a@ %a)@]" Kind.pp kind pp_typ t
      | ExistsRepT (kind, t) ->
          fprintf ff "@[<2>(exists.rep@ %a@ %a)@]" Kind.pp kind pp_typ t
      | ExistsSizeT (kind, t) ->
          fprintf ff "@[<2>(exists.size@ %a@ %a)@]" Kind.pp kind pp_typ t
      | ExistsTypeT (k1, k2, t) ->
          fprintf ff "@[<2>(exists.type@ %a@ %a@ %a)@]" Kind.pp k1 Kind.pp k2
            pp_typ t

    and pp_function_typ ff = function
      | MonoFunT (t1s, t2s) ->
          fprintf ff "@[(%a->%a)@]"
            (pp_print_list_post_space pp_typ)
            t1s
            (pp_print_list_pre_space pp_typ)
            t2s
      | ForallMemT ft ->
          fprintf ff "@[<2>(forall.mem@ %a)@]" pp_rocq_function_typ ft
      | ForallRepT ft ->
          fprintf ff "@[<2>(forall.rep@ %a)@]" pp_rocq_function_typ ft
      | ForallSizeT ft ->
          fprintf ff "@[<2>(forall.size@ %a)@]" pp_rocq_function_typ ft
      | ForallTypeT (kind, ft) ->
          fprintf ff "@[<2>(forall.type@ %a@ %a)@]" Kind.pp_rocq kind
            pp_rocq_function_typ ft
  end
end

module Type = struct
  include Internal.Types

  type t = Internal.Types.typ [@@deriving eq, ord, sexp]

  let pp_sexp = Internal.Types.pp_sexp_typ
  let pp_rocq = Internal.Types.pp_rocq_typ
  let pp = Internal.Types.pp_typ
  let subst = Richwasm_extract.Rw.Core.subst_type
  let ren = Richwasm_extract.Rw.Core.ren_type
end

module FunctionType = struct
  include Internal.Types

  type t = Internal.Types.function_typ [@@deriving eq, ord, sexp]

  let pp_sexp = Internal.Types.pp_sexp_function_typ
  let pp_rocq = Internal.Types.pp_rocq_function_typ
  let pp = Internal.Types.pp_function_typ
  let subst = Richwasm_extract.Rw.Core.subst_function_type
  let ren = Richwasm_extract.Rw.Core.ren_function_type
end

module InstructionType = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.instruction_type[@with coq_type := Type.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | InstrT (t_in, t_out) ->
        fprintf ff "@[<2>(InstrT@ %a@ %a)@]"
          (pp_rocq_list Type.pp_rocq)
          t_in
          (pp_rocq_list Type.pp_rocq)
          t_out

  let pp ff : t -> _ = function
    | InstrT (t_in, t_out) ->
        fprintf ff "@[[%a]@ ->@ [%a]@]"
          (pp_print_list_space Type.pp)
          t_in
          (pp_print_list_space Type.pp)
          t_out

  let subst = Richwasm_extract.Rw.Core.subst_function_type
end

module Index = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.index
      [@with
        memory := Memory.t;
        representation := Representation.t;
        size := Size.t;
        coq_type := Type.t;
        instruction_type := InstructionType.t;
        function_type := FunctionType.t])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff : t -> _ = function
    | MemI mem -> fprintf ff "@[<2>(MemI@ %a)@]" Memory.pp_rocq mem
    | RepI rep -> fprintf ff "@[<2>(RepI@ %a)@]" Representation.pp_rocq rep
    | SizeI size -> fprintf ff "@[<2>(SizeI@ %a)@]" Size.pp_rocq size
    | TypeI typ -> fprintf ff "@[<2>(TypeI@ %a)@]" Type.pp_rocq typ

  let pp ff : t -> _ = function
    | MemI mem -> fprintf ff "@[<2>(mem@ %a)@]" Memory.pp mem
    | RepI rep -> fprintf ff "@[<2>(rep@ %a)@]" Representation.pp rep
    | SizeI sz -> fprintf ff "@[<2>(size@ %a)@]" Size.pp sz
    | TypeI ty -> fprintf ff "@[<2>(type@ %a)@]" Type.pp ty
end

module Consumption = struct
  type t = [%import: Richwasm_extract.Rw.Core.consumption]
  [@@deriving eq, ord, sexp]

  let pp_rocq ff : t -> _ = function
    | Copy -> fprintf ff "Copy"
    | Move -> fprintf ff "Move"

  let pp ff : t -> _ = function
    | Copy -> fprintf ff "copy"
    | Move -> fprintf ff "move"
end

module Instruction = struct
  type t =
    [%import:
      (Richwasm_extract.Rw.Core.instruction
      [@with
        instruction_type := InstructionType.t;
        num_instruction := NumInstruction.t;
        coq_type := Type.t;
        index := Index.t;
        consumption := Consumption.t;
        path := Path.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp_rocq ff : t -> _ =
    let pp_it = InstructionType.pp_rocq in
    let pp_lfx = pp_print_list Type.pp_rocq in
    let pp_instrs = pp_rocq_list pp_rocq in
    function
    | INop it -> fprintf ff "@[<2>(INop@ %a)@]" pp_it it
    | IUnreachable it -> fprintf ff "@[<2>(IUnreachable@ %a)@]" pp_it it
    | ICopy it -> fprintf ff "@[<2>(ICopy@ %a)@]" pp_it it
    | IDrop it -> fprintf ff "@[<2>(IDrop@ %a)@]" pp_it it
    | INum (it, ni) ->
        fprintf ff "@[<2>(INum@ %a@ %a)@]" pp_it it NumInstruction.pp_rocq ni
    | INumConst (it, i) ->
        fprintf ff "@[<2>(INumConst@ %a@ %a)@]" pp_it it Z.pp_print i
    | IBlock (it, lfx, instrs) ->
        fprintf ff "@[<2>(IBlock@ %a@ %a@ %a)@]" pp_it it pp_lfx lfx pp_instrs
          instrs
    | ILoop (it, instrs) ->
        fprintf ff "@[<2>(ILoop@ %a@ %a)@]" pp_it it pp_instrs instrs
    | IIte (it, lfx, e_thn, e_els) ->
        fprintf ff "@[<2>(IIte@ %a@ %a@ %a@ %a)@]" pp_it it pp_lfx lfx pp_instrs
          e_thn pp_instrs e_els
    | IBr (it, i) -> fprintf ff "@[<2>(IBr@ %a@ %a)@]" pp_it it Z.pp_print i
    | IReturn it -> fprintf ff "@[<2>(IReturn@ %a)@]" pp_it it
    | ILocalGet (it, i) ->
        fprintf ff "@[<2>(ILocalGet@ %a@ %a)@]" pp_it it Z.pp_print i
    | ILocalSet (it, i) ->
        fprintf ff "@[<2>(ILocalSet@ %a@ %a)@]" pp_it it Z.pp_print i
    | ICodeRef (it, i) ->
        fprintf ff "@[<2>(ICodeRef@ %a@ %a)@]" pp_it it Z.pp_print i
    | IInst (it, idx) ->
        fprintf ff "@[<2>(IInst@ %a@ %a)@]" pp_it it Index.pp_rocq idx
    | ICall (it, i, idxs) ->
        fprintf ff "@[<2>(ICall@ %a@ %a@ %a)@]" pp_it it Z.pp_print i
          (pp_rocq_list Index.pp_rocq)
          idxs
    | ICallIndirect it -> fprintf ff "@[<2>(ICallIndirect@ %a)@]" pp_it it
    | IInject (it, i) ->
        fprintf ff "@[<2>(IInject@ %a@ %a)@]" pp_it it Z.pp_print i
    | IInjectNew (it, i) ->
        fprintf ff "@[<2>(IInjectNew@ %a@ %a)@]" pp_it it Z.pp_print i
    | ICase (it, lfx, cases) ->
        fprintf ff "@[<2>(ICase@ %a@ %a@ %a)@]" pp_it it pp_lfx lfx
          (pp_rocq_list pp_instrs) cases
    | ICaseLoad (it, c, lfx, cases) ->
        fprintf ff "@[<2>(ICaseLoad@ %a@ %a@ %a@ %a)@]" pp_it it
          Consumption.pp_rocq c pp_lfx lfx (pp_rocq_list pp_instrs) cases
    | IGroup it -> fprintf ff "@[<2>(IGroup@ %a)@]" pp_it it
    | IUngroup it -> fprintf ff "@[<2>(IUngroup@ %a)@]" pp_it it
    | IFold it -> fprintf ff "@[<2>(IFold@ %a)@]" pp_it it
    | IUnfold it -> fprintf ff "@[<2>(IUnfold@ %a)@]" pp_it it
    | IPack it -> fprintf ff "@[<2>(IPack@ %a)@]" pp_it it
    | IUnpack (it, lfx, instrs) ->
        fprintf ff "@[<2>(IUnpack@ %a@ %a@ %a)@]" pp_it it pp_lfx lfx pp_instrs
          instrs
    | ITag it -> fprintf ff "@[<2>(ITag@ %a)@]" pp_it it
    | IUntag it -> fprintf ff "@[<2>(IUntag@ %a)@]" pp_it it
    | ICast it -> fprintf ff "@[<2>(ICast@ %a)@]" pp_it it
    | INew it -> fprintf ff "@[<2>(INew@ %a)@]" pp_it it
    | ILoad (it, p, c) ->
        fprintf ff "@[<2>(ILoad@ %a@ %a@ %a)@]" pp_it it
          (pp_rocq_list Z.pp_print) p Consumption.pp_rocq c
    | IStore (it, p) ->
        fprintf ff "@[<2>(IStore@ %a@ %a)" pp_it it (pp_rocq_list Z.pp_print) p
    | ISwap (it, p) ->
        fprintf ff "@[<2>(ISwap@ %a@ %a)@]" pp_it it (pp_rocq_list Z.pp_print) p

  let rec pp ff : t -> _ =
    let pp_instrs ff (instrs : t list) =
      List.iteri
        ~f:(fun i -> if i = 0 then fprintf ff "%a" pp else fprintf ff "@,%a" pp)
        instrs
    in
    let pp_int = Z.pp_print in
    let pp_it_comment ff x = fprintf ff " ;; @[%a@]" InstructionType.pp x in
    let pp_lfx ff x =
      fprintf ff "@[<2>(localfx";
      List.iteri
        ~f:(fun idx typ -> fprintf ff "@ @[[%i@ =>@ %a]@]" idx Type.pp typ)
        x;
      fprintf ff ")@]"
    in
    let pp_path ff x =
      fprintf ff "(path%a)" (pp_print_list_pre_space pp_int) x
    in
    function
    | INop it -> fprintf ff "nop%a" pp_it_comment it
    | IUnreachable it -> fprintf ff "unreachable%a" pp_it_comment it
    | ICopy it -> fprintf ff "copy%a" pp_it_comment it
    | IDrop it -> fprintf ff "drop%a" pp_it_comment it
    | INum (it, ni) -> fprintf ff "%a%a" NumInstruction.pp ni pp_it_comment it
    | INumConst (it, n) -> fprintf ff "num_const %a%a" pp_int n pp_it_comment it
    | IBlock (it, lfx, instrs) ->
        fprintf ff "@[<v 0>@[<2>block@ %a@]@,@[<v 2>  %a@]@,end@]%a" pp_lfx lfx
          pp_instrs instrs pp_it_comment it
    | ILoop (it, instrs) ->
        fprintf ff "@[<v 0>loop@,@[<v 2>  %a@]@,end@]%a" pp_instrs instrs
          pp_it_comment it
    | IIte (it, lfx, e_thn, e_els) ->
        fprintf ff
          "@[<v 0>@[<2>if@ %a@]@,@[<v 2>  %a@]@,else@,@[<v 2>  %a@]@,end@]%a"
          pp_lfx lfx pp_instrs e_thn pp_instrs e_els pp_it_comment it
    | IBr (it, i) -> fprintf ff "@[<2>br@ %a@]%a" pp_int i pp_it_comment it
    | IReturn it -> fprintf ff "return%a" pp_it_comment it
    | ILocalGet (it, i) ->
        fprintf ff "@[<2>local.get@ %a@]%a" pp_int i pp_it_comment it
    | ILocalSet (it, i) ->
        fprintf ff "@[<2>local.set@ %a@]%a" pp_int i pp_it_comment it
    | ICodeRef (it, i) ->
        fprintf ff "@[<2>coderef@ %a@]%a" pp_int i pp_it_comment it
    | IInst (it, idx) ->
        fprintf ff "@[<2>inst@ %a@]%a" Index.pp idx pp_it_comment it
    | ICall (it, i, idxs) ->
        fprintf ff "@[<2>call@ %a@ (inst%a)@]%a" pp_int i
          (pp_print_list_pre_space Index.pp)
          idxs pp_it_comment it
    | ICallIndirect it -> fprintf ff "call_indirect%a" pp_it_comment it
    | IInject (it, i) ->
        fprintf ff "@[<2>inject@ %a@]%a" pp_int i pp_it_comment it
    | IInjectNew (it, i) ->
        fprintf ff "@[<2>inject_new@ %a@]%a" pp_int i pp_it_comment it
    | ICase (it, lfx, cases) ->
        fprintf ff "@[<v 0>@[<2>case@ %a@]@,@[<v 2>  " pp_lfx lfx;
        List.iteri
          ~f:(fun i instrs ->
            if i <> 0 then fprintf ff "@,";
            fprintf ff "@[<v 2>(%a@,%a)@]" Base.Int.pp i pp_instrs instrs)
          cases;
        fprintf ff "@]@,end@]%a" pp_it_comment it
    | ICaseLoad (it, consume, lfx, cases) ->
        fprintf ff "@[<v 0>@[<2>case_load@ %a@ %a@]@,@[<v 2>  " Consumption.pp
          consume pp_lfx lfx;
        List.iteri
          ~f:(fun i instrs ->
            if i <> 0 then fprintf ff "@,";
            fprintf ff "@[<v 2>(%a@,%a)@]" Base.Int.pp i pp_instrs instrs)
          cases;
        fprintf ff "@]@,end@]%a" pp_it_comment it
    | IGroup it -> fprintf ff "group%a" pp_it_comment it
    | IUngroup it -> fprintf ff "ungroup%a" pp_it_comment it
    | IFold it -> fprintf ff "fold%a" pp_it_comment it
    | IUnfold it -> fprintf ff "unfold%a" pp_it_comment it
    | IPack it -> fprintf ff "pack%a" pp_it_comment it
    | IUnpack (it, lfx, instrs) ->
        fprintf ff "@[<v 0>@[<2>unpack %a@]@,@[<v 2>  %a@]@,end@]%a" pp_lfx lfx
          pp_instrs instrs pp_it_comment it
    | ITag it -> fprintf ff "tag%a" pp_it_comment it
    | IUntag it -> fprintf ff "untag%a" pp_it_comment it
    | ICast it -> fprintf ff "cast%a" pp_it_comment it
    | INew it -> fprintf ff "new%a" pp_it_comment it
    | ILoad (it, p, c) ->
        fprintf ff "@[<2>load@ %a@ %a@]%a" pp_path p Consumption.pp c
          pp_it_comment it
    | IStore (it, p) ->
        fprintf ff "@[<2>store@ %a@]%a" pp_path p pp_it_comment it
    | ISwap (it, p) -> fprintf ff "@[<2>swap@ %a@]%a" pp_path p pp_it_comment it

  let subst = Richwasm_extract.Rw.Core.subst_instruction
end

module Module = struct
  module Function = struct
    type t =
      [%import:
        (Richwasm_extract.Module.module_function
        [@with
          Richwasm_extract.Rw.Core.function_type := FunctionType.t;
          Richwasm_extract.Rw.Core.representation := Representation.t;
          Richwasm_extract.Rw.Core.instruction := Instruction.t])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff ({ mf_type; mf_locals; mf_body } : t) : unit =
      fprintf ff "@[<v 0>{|@,@[<hv 2>  ";
      fprintf ff "@[<2>mf_type :=@ %a;@]@ " FunctionType.pp_rocq mf_type;
      fprintf ff "@[<2>mf_locals :=@ %a;@]@ "
        (pp_rocq_list Representation.pp_rocq)
        mf_locals;
      fprintf ff "@[<2>mf_body :=@ %a@];"
        (pp_rocq_list Instruction.pp_rocq)
        mf_body;
      fprintf ff "@]@,|}@]"

    let pp ff ({ mf_type; mf_locals; mf_body } : t) : unit =
      fprintf ff "@[<v 2>@[<4>(func@ %a" FunctionType.pp mf_type;
      if not @@ List.is_empty mf_locals then
        fprintf ff "@ (local%a)"
          (pp_print_list_pre_space Representation.pp)
          mf_locals;
      fprintf ff "@]";
      List.iter ~f:(fprintf ff "@,%a" Instruction.pp) mf_body;
      fprintf ff ")@]"
  end

  module Export = struct
    type t =
      [%import:
        (Richwasm_extract.Module.module_export
        [@with Big_int_Z.big_int := Big_int_Z'.big_int])]
    [@@deriving eq, ord, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp_rocq ff ({ me_name; me_desc } : t) : unit =
      fprintf ff "@[<v 0>{|@,@[<hv 2>  ";
      fprintf ff "@[<2>me_name :=@ %a;@]@ " String.pp me_name;
      fprintf ff "@[<2>me_desc :=@ %a;@]@ " Z.pp_print me_desc;
      fprintf ff "@]@,|}@]"

    let pp ff ({ me_name; me_desc } : t) : unit =
      let pp_desc ff funcidx = fprintf ff "(@[func %a@])" Z.pp_print funcidx in
      fprintf ff "(@[export %a@ %a@])" String.pp me_name pp_desc me_desc
  end

  type t =
    [%import:
      (Richwasm_extract.Module.coq_module
      [@with
        Richwasm_extract.Rw.Core.function_type := FunctionType.t;
        module_function := Function.t;
        module_export := Export.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp_rocq ff ({ m_imports; m_functions; m_table; m_exports } : t) : unit =
    fprintf ff "@[<v 0>{|@,@[<hv 2>  ";
    fprintf ff "@[<2>m_imports :=@ %a;@]@ "
      (pp_rocq_list FunctionType.pp_rocq)
      m_imports;
    fprintf ff "@[<2>m_functions :=@ %a;@]@ "
      (pp_rocq_list Function.pp_rocq)
      m_functions;
    fprintf ff "@[<2>m_table :=@ %a;@]@ " (pp_rocq_list Z.pp_print) m_table;
    fprintf ff "@[<2>m_exports :=@ %a;@]"
      (pp_rocq_list Export.pp_rocq)
      m_exports;
    fprintf ff "@]@,|}@]"

  let pp ff ({ m_imports; m_functions; m_table; m_exports } : t) : unit =
    let ppl_pre_cut = pp_print_list_pre in
    let ppl_pre_space = pp_print_list_pre_space in
    fprintf ff "@[<v 2>@[(module @]%a%a@,(table@[<2>%a@])%a)@]"
      (ppl_pre_cut (fun ff -> fprintf ff "(import %a)" FunctionType.pp))
      m_imports (ppl_pre_cut Function.pp) m_functions (ppl_pre_space Z.pp_print)
      m_table (ppl_pre_cut Export.pp) m_exports
end
