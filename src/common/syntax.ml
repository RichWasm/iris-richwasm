open! Base
open! Stdlib.Format

module Copyability = struct
  type t =
    | NoCopy
    | ExCopy
    | ImCopy
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | NoCopy -> fprintf ff "nocopy"
    | ExCopy -> fprintf ff "excopy"
    | ImCopy -> fprintf ff "imcopy"
end

module Dropability = struct
  type t =
    | NoDrop
    | ExDrop
    | ImDrop
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | NoDrop -> fprintf ff "nodrop"
    | ExDrop -> fprintf ff "exdrop"
    | ImDrop -> fprintf ff "imdrop"
end

module Memory = struct
  type t =
    | MM
    | GC
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | MM -> fprintf ff "mm"
    | GC -> fprintf ff "gc"
end

module PrimitiveRep = struct
  type t =
    | Ptr
    | I32
    | I64
    | F32
    | F64
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Representation = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Prim of PrimitiveRep.t
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Size = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Rep of Representation.t
    | Const of int
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Sizity = struct
  type t =
    | Sized of Size.t
    | Unsized
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Kind = struct
  type t =
    | VALTYPE of Representation.t * Copyability.t * Dropability.t
    | MEMTYPE of Sizity.t * Memory.t * Dropability.t
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Quantifier = struct
  type t =
    | Memory
    | Representation
    | Size
    | Type of Kind.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Memory -> fprintf ff "mem"
    | Representation -> fprintf ff "rep"
    | Size -> fprintf ff "size"
    | Type k -> fprintf ff "type %a" Kind.pp k
end

module Sign = struct
  type t =
    | Unsigned
    | Signed
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Unsigned -> fprintf ff "u"
    | Signed -> fprintf ff "s"
end

module Int = struct
  module Type = struct
    type t =
      | I32
      | I64
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | I32 -> fprintf ff "i32"
      | I64 -> fprintf ff "i64"
  end

  module Unop = struct
    type t =
      | Clz
      | Ctz
      | Popcnt
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | Clz -> fprintf ff "clz"
      | Ctz -> fprintf ff "ctz"
      | Popcnt -> fprintf ff "popcnt"
  end

  module Binop = struct
    type t =
      | Add
      | Sub
      | Mul
      | Div of Sign.t
      | Rem of Sign.t
      | And
      | Or
      | Xor
      | Shl
      | Shr of Sign.t
      | Rotl
      | Rotr
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | Add -> fprintf ff "add"
      | Sub -> fprintf ff "sub"
      | Mul -> fprintf ff "mul"
      | Div s -> fprintf ff "div_%a" Sign.pp s
      | Rem s -> fprintf ff "rem_%a" Sign.pp s
      | And -> fprintf ff "and"
      | Or -> fprintf ff "or"
      | Xor -> fprintf ff "xor"
      | Shl -> fprintf ff "shl"
      | Shr s -> fprintf ff "shr_%a" Sign.pp s
      | Rotl -> fprintf ff "rotl"
      | Rotr -> fprintf ff "rotr"
  end

  module Testop = struct
    type t = Eqz [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | Eqz -> fprintf ff "eqz"
  end

  module Relop = struct
    type t =
      | Eq
      | Ne
      | Lt of Sign.t
      | Gt of Sign.t
      | Le of Sign.t
      | Ge of Sign.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | Eq -> fprintf ff "eq"
      | Ne -> fprintf ff "ne"
      | Lt s -> fprintf ff "lt_%a" Sign.pp s
      | Gt s -> fprintf ff "gt_%a" Sign.pp s
      | Le s -> fprintf ff "le_%a" Sign.pp s
      | Ge s -> fprintf ff "ge_%a" Sign.pp s
  end
end

module Float = struct
  module Type = struct
    type t =
      | F32
      | F64
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | F32 -> fprintf ff "f32"
      | F64 -> fprintf ff "f64"
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

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff : t -> unit = function
      | Neg -> fprintf ff "neg"
      | Abs -> fprintf ff "abs"
      | Ceil -> fprintf ff "ceil"
      | Floor -> fprintf ff "floor"
      | Trunc -> fprintf ff "trunc"
      | Nearest -> fprintf ff "nearest"
      | Sqrt -> fprintf ff "sqrt"
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

    let pp ff : t -> unit = function
      | Add -> fprintf ff "add"
      | Sub -> fprintf ff "sub"
      | Mul -> fprintf ff "mul"
      | Div -> fprintf ff "div"
      | Min -> fprintf ff "min"
      | Max -> fprintf ff "max"
      | CopySign -> fprintf ff "copysign"
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

    let pp ff : t -> unit = function
      | Eq -> fprintf ff "eq"
      | Ne -> fprintf ff "ne"
      | Lt -> fprintf ff "lt"
      | Gt -> fprintf ff "gt"
      | Le -> fprintf ff "le"
      | Ge -> fprintf ff "ge"
  end
end

module NumType = struct
  type t =
    | Int of Int.Type.t
    | Float of Float.Type.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Int it -> Int.Type.pp ff it
    | Float ft -> Float.Type.pp ff ft
end

module ConversionOp = struct
  type t =
    | Wrap
    | Extend of Sign.t
    | Trunc of Float.Type.t * Int.Type.t * Sign.t
    | Demote
    | Promote
    | Convert of Int.Type.t * Float.Type.t * Sign.t
    | Reinterpret of NumType.t
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Wrap -> fprintf ff "i32.wrap_i64"
    | Extend s -> fprintf ff "i64.extend_i32_%a" Sign.pp s
    | Trunc (ft, it, sign) ->
        fprintf ff "%a.trunc_%a_%a" Int.Type.pp it Float.Type.pp ft Sign.pp sign
    | Demote -> fprintf ff "f32.demote_f64"
    | Promote -> fprintf ff "f64.promote_f32"
    | Convert (it, ft, sign) ->
        fprintf ff "%a.convert_%a_%a" Float.Type.pp ft Int.Type.pp it Sign.pp
          sign
    | Reinterpret (Int I32) -> fprintf ff "f32.reinterpret_i32"
    | Reinterpret (Int I64) -> fprintf ff "f64.reinterpret_i64"
    | Reinterpret (Float F32) -> fprintf ff "i32.reinterpret_f32"
    | Reinterpret (Float F64) -> fprintf ff "i64.reinterpret_f64"
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

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Int1 (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Unop.pp o
    | Int2 (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Binop.pp o
    | IntTest (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Testop.pp o
    | IntRel (t, o) -> fprintf ff "%a.%a" Int.Type.pp t Int.Relop.pp o
    | Float1 (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Unop.pp o
    | Float2 (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Binop.pp o
    | FloatRel (t, o) -> fprintf ff "%a.%a" Float.Type.pp t Float.Relop.pp o
    | Cvt o -> fprintf ff "%a" ConversionOp.pp o
end

module rec Type : sig
  type t =
    | Var of int
    | I31
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

  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
end = struct
  type t =
    | Var of int
    | I31
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
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
  let show_pp = pp

  let rec pp ff : t -> unit = function
    | Var i -> fprintf ff "@[(var %a)@]" Base.Int.pp i
    | I31 -> fprintf ff "i31"
    | Num nt -> fprintf ff "%a" NumType.pp nt
    | Sum ts ->
        fprintf ff "@[(sum";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Prod ts ->
        fprintf ff "@[(prod";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Ref (m, t) -> fprintf ff "@[(ref %a %a)@]" Memory.pp m pp t
    | x -> show_pp ff x
  (*| GCPtr t -> fprintf ff ""
    | CodeRef ft -> fprintf ff ""
    | Rep (r, t) -> fprintf ff ""
    | Pad (s, t) -> fprintf ff ""
    | Ser t -> fprintf ff ""
    | Rec t -> fprintf ff ""
    | Exists (q, t) -> fprintf ff "" *)
end

and FunctionType : sig
  type t = FunctionType of Quantifier.t list * Type.t list * Type.t list
  [@@deriving eq, ord, iter, map, fold, sexp]

  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
end = struct
  type t = FunctionType of Quantifier.t list * Type.t list * Type.t list
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff (FunctionType (quals, ts1, ts2)) =
    let rec go = function
      | [] ->
          List.iter ~f:(fprintf ff "%a@ " Type.pp) ts1;
          fprintf ff "->";
          List.iter ~f:(fprintf ff "@ %a" Type.pp) ts2
      | x :: xs ->
          fprintf ff "@[(forall.%a" Quantifier.pp x;
          go xs;
          fprintf ff ")@]"
    in
    go quals
end

module BlockType = struct
  type t = BlockType of Type.t list
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp ff (BlockType res : t) : unit =
    fprintf ff "(@[result";
    List.iter ~f:(fprintf ff "@ %a" Type.pp) res;
    fprintf ff "@])"
end

module LocalFx = struct
  type t = LocalFx of (int * Type.t) list
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Index = struct
  type t =
    | Mem of Memory.t
    | Rep of Representation.t
    | Size of Size.t
    | Type of Type.t
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Path = struct
  module Component = struct
    type t =
      | Proj of int
      | Unwrap
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  type t = Path of Component.t list
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Instruction = struct
  type t =
    | Nop
    | Unreachable
    | Copy
    | Drop
    | Num of NumInstruction.t
    | NumConst of NumType.t * int
    | Block of BlockType.t * LocalFx.t * t list
    | Loop of BlockType.t * t list
    | Ite of BlockType.t * LocalFx.t * t list * t list
    | Br of int
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
    | Case of BlockType.t * LocalFx.t * t list list
    | Group of int
    | Ungroup
    | Fold of Type.t
    | Unfold
    | Pack of Index.t * Type.t
    | Unpack of BlockType.t * LocalFx.t * t list
    | Wrap of Type.t
    | Unwrap
    | Tag
    | Untag
    | RefNew of Memory.t * Type.t
    | RefLoad of Path.t * Type.t
    | RefStore of Path.t
    | RefSwap of Path.t
  [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
  let show_pp = pp

  let rec pp ff : t -> unit =
    let pp_instrs ff (instrs : t list) = () in
    let pp_int = Base.Int.pp in
    function
    | Nop -> fprintf ff "nop"
    | Unreachable -> fprintf ff "unreachable"
    | Copy -> fprintf ff "copy"
    | Drop -> fprintf ff "drop"
    | Num ni -> fprintf ff "%a" NumInstruction.pp ni
    | NumConst (t, n) -> fprintf ff "%a.const %a" NumType.pp t pp_int n
    (*| Block (it, lfx, instrs) ->
    (* TODO: block return *)
        fprintf ff "block %a %a @; @[<v 2>%a@] end" InstructionType.pp it
          LocalFx.pp lfx pp_instrs instrs *)
    | Br i -> fprintf ff "br %a" pp_int i
    | Return -> fprintf ff "return"
    | LocalGet i -> fprintf ff "local.get %a" pp_int i
    | LocalSet i -> fprintf ff "local.set %a" pp_int i
    | GlobalGet i -> fprintf ff "global.get %a" pp_int i
    | GlobalSet i -> fprintf ff "global.set %a" pp_int i
    | GlobalSwap i -> fprintf ff "global.swap %a" pp_int i
    | CodeRef i -> fprintf ff "coderef %a" pp_int i
    | Group i -> fprintf ff "seq.group %a" pp_int i
    | Ungroup -> fprintf ff "seq.ungroup"
    | Wrap t -> fprintf ff "wrap %a" Type.pp t
    | Unwrap -> fprintf ff "unwrap"
    | Tag -> fprintf ff "tag"
    | Untag -> fprintf ff "untag"
    | RefNew (m, t) -> fprintf ff "ref.new %a %a" Memory.pp m Type.pp t
    | RefLoad (p, t) -> fprintf ff "ref.load %a %a" Path.pp p Type.pp t
    | RefStore p -> fprintf ff "ref.store %a" Path.pp p
    | RefSwap p -> fprintf ff "ref.swap %a" Path.pp p
    | x -> show_pp ff x
end

module Mutability = struct
  type t =
    | Mut
    | Imm
  [@@deriving eq, ord, iter, map, fold, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Mut -> fprintf ff "mut"
    | Imm -> fprintf ff "imm"
end

module Module = struct
  module Import = struct
    module Desc = struct
      type t =
        | ImFunction of FunctionType.t
        | ImGlobal of Mutability.t * Type.t
      [@@deriving eq, ord, iter, map, fold, sexp]

      let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

      let pp ff : t -> unit = function
        | ImFunction ft -> fprintf ff "@[(func %a)@]" FunctionType.pp ft
        | ImGlobal (mut, typ) ->
            fprintf ff "@[(global %a %a)@]" Mutability.pp mut Type.pp typ
    end

    type t = {
      name : string;
      desc : Desc.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff ({ name; desc } : t) : unit =
      fprintf ff "@[(import %s %a)@]" name Desc.pp desc
  end

  module Global = struct
    type t = {
      mut : Mutability.t;
      typ : Type.t;
      init : Instruction.t list;
    }
    [@@deriving eq, ord, iter, map, fold, sexp, show { with_path = false }]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Function = struct
    type t = {
      typ : FunctionType.t;
      locals : Representation.t list;
      body : Instruction.t list;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff ({ typ; locals; body } : t) : unit =
      fprintf ff "@[<v 2>@[(func %a" FunctionType.pp typ;
      if not @@ List.is_empty locals then (
        fprintf ff "@[(local";
        List.iter ~f:(fprintf ff "@ %a" Representation.pp) locals;
        fprintf ff "@]");
      fprintf ff "@]";
      List.iter ~f:(fprintf ff "@;%a" Instruction.pp) body;
      fprintf ff "@[)@]@]"
  end

  module Export = struct
    module Desc = struct
      type t =
        | ExFunction of int
        | ExGlobal of int
      [@@deriving eq, ord, iter, map, fold, sexp]

      let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

      let pp ff : t -> unit = function
        | ExFunction i -> fprintf ff "@[(func %a)@]" Base.Int.pp i
        | ExGlobal i -> fprintf ff "@[(global %a)@]" Base.Int.pp i
    end

    type t = {
      name : string;
      desc : Desc.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff ({ name; desc } : t) : unit =
      fprintf ff "@[(export %s %a)@]" name Desc.pp desc
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

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff ({ imports; globals; functions; table; start; exports } : t) : unit
      =
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
    print_sep ~f:(Import.pp ff) ~sep:break_hint imports;
    print_sep ~f:(Global.pp ff) ~sep:break_hint globals;
    print_sep ~f:(Function.pp ff) ~sep:break_hint functions;
    fprintf ff "@;@[(table@[<hv 2>";
    if List.is_empty table then () else fprintf ff "@ ";
    print_sep ~f:(Base.Int.pp ff) ~sep:space_hint table;
    fprintf ff "@])@]";
    Option.iter
      ~f:(fun start -> fprintf ff "@;(start %a)" Base.Int.pp start)
      start;
    print_sep ~f:(Export.pp ff) ~sep:break_hint exports;
    fprintf ff "@])@]"
end
