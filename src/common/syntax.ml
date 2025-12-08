open! Base
open! Stdlib.Format

module Unscoped = struct
  let scons (x : 'a) (xi : int -> 'a) (n : int) : 'a =
    if n = 0 then x else xi (n - 1)

  let rec map f = function
    | [] -> []
    | a :: l0 -> f a :: map f l0

  let funcomp g f x = g (f x)
  let id = Fn.id
  let shift = ( + ) 1
  let var_zero = 0

  let up_ren (xi : int -> int) : int -> int =
    scons 0 (funcomp (fun x -> x + 1) xi)
end

module Copyability = struct
  type t =
    | NoCopy
    | ExCopy
    | ImCopy
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | NoCopy -> fprintf ff "nocopy"
    | ExCopy -> fprintf ff "excopy"
    | ImCopy -> fprintf ff "imcopy"
end

module Dropability = struct
  type t =
    | ExDrop
    | ImDrop
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | ExDrop -> fprintf ff "exdrop"
    | ImDrop -> fprintf ff "imdrop"
end

module BaseMemory = struct
  type t =
    | MM
    | GC
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | MM -> fprintf ff "mm"
    | GC -> fprintf ff "gc"
end

module Memory = struct
  type t =
    | Var of int
    | Base of BaseMemory.t
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff : t -> unit = function
    | Var i -> fprintf ff "@[(var %a)@]" Base.Int.pp i
    | Base m -> fprintf ff "@[(base %a)@]" BaseMemory.pp m

  (* autosubst: *)
  open Unscoped

  let ren xi_memory = function
    | Var s0 -> Var (xi_memory s0)
    | Base s0 -> Base s0

  let subst sigma_memory = function
    | Var s0 -> sigma_memory s0
    | Base s0 -> Base s0

  let up_memory sigma = scons (Var var_zero) (funcomp (ren shift) sigma)
  let up_representation sigma = funcomp (ren id) sigma
  let up_size sigma = funcomp (ren id) sigma
  let up_type sigma = funcomp (ren id) sigma
end

module AtomicRep = struct
  type t =
    | Ptr
    | I32
    | I64
    | F32
    | F64
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff = function
    | Ptr -> fprintf ff "ptr"
    | I32 -> fprintf ff "i32"
    | I64 -> fprintf ff "i64"
    | F32 -> fprintf ff "f32"
    | F64 -> fprintf ff "f64"
end

module Representation = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Atom of AtomicRep.t
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff = function
    | Var x -> fprintf ff "@[(var %a)@]" Base.Int.pp x
    | Sum rs ->
        fprintf ff "@[(sum";
        List.iter ~f:(fprintf ff "@ %a" pp) rs;
        fprintf ff ")@]"
    | Prod rs ->
        fprintf ff "@[(prod";
        List.iter ~f:(fprintf ff "@ %a" pp) rs;
        fprintf ff ")@]"
    | Atom prim -> AtomicRep.pp ff prim

  (* autosubst: *)
  open Unscoped

  let rec ren xi_representation = function
    | Var s0 -> Var (xi_representation s0)
    | Sum s0 -> Sum (map (ren xi_representation) s0)
    | Prod s0 -> Prod (map (ren xi_representation) s0)
    | Atom s0 -> Atom s0

  let rec subst sigma_representation = function
    | Var s0 -> sigma_representation s0
    | Sum s0 -> Sum (map (subst sigma_representation) s0)
    | Prod s0 -> Prod (map (subst sigma_representation) s0)
    | Atom s0 -> Atom s0

  let up_memory sigma = funcomp (ren id) sigma
  let up_representation sigma = scons (Var var_zero) (funcomp (ren shift) sigma)
  let up_size sigma = funcomp (ren id) sigma
  let up_type sigma = funcomp (ren id) sigma
end

module Size = struct
  type t =
    | Var of int
    | Sum of t list
    | Prod of t list
    | Rep of Representation.t
    | Const of int
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff = function
    | Var x -> fprintf ff "@[(var %a)@]" Base.Int.pp x
    | Sum rs ->
        fprintf ff "@[(sum";
        List.iter ~f:(fprintf ff "@ %a" pp) rs;
        fprintf ff ")@]"
    | Prod rs ->
        fprintf ff "@[(prod";
        List.iter ~f:(fprintf ff "@ %a" pp) rs;
        fprintf ff ")@]"
    | Rep r -> fprintf ff "@[(rep %a)@]" Representation.pp r
    | Const prim -> fprintf ff "@[(const %a)@]" Base.Int.pp prim

  (* autosubst: *)
  open Unscoped

  let rec ren xi_representation xi_size = function
    | Var s0 -> Var (xi_size s0)
    | Sum s0 -> Sum (map (ren xi_representation xi_size) s0)
    | Prod s0 -> Prod (map (ren xi_representation xi_size) s0)
    | Rep s0 -> Rep (Representation.ren xi_representation s0)
    | Const s0 -> Const s0

  let rec subst sigma_representation sigma_size = function
    | Var s0 -> sigma_size s0
    | Sum s0 -> Sum (map (subst sigma_representation sigma_size) s0)
    | Prod s0 -> Prod (map (subst sigma_representation sigma_size) s0)
    | Rep s0 -> Rep (Representation.subst sigma_representation s0)
    | Const s0 -> Const s0

  let up_memory sigma = funcomp (ren id id) sigma
  let up_representation sigma = funcomp (ren shift id) sigma
  let up_size sigma = scons (Var var_zero) (funcomp (ren id shift) sigma)
  let up_type sigma = funcomp (ren id id) sigma
end

module Kind = struct
  type t =
    | VALTYPE of Representation.t * Copyability.t * Dropability.t
    | MEMTYPE of Size.t * Dropability.t
  [@@deriving eq, ord, variants, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  (* autosubst: *)

  let ren xi_representation xi_size = function
    | VALTYPE (s0, s1, s2) ->
        VALTYPE (Representation.ren xi_representation s0, s1, s2)
    | MEMTYPE (s0, s1) -> MEMTYPE (Size.ren xi_representation xi_size s0, s1)

  let subst sigma_representation sigma_size = function
    | VALTYPE (s0, s1, s2) ->
        VALTYPE (Representation.subst sigma_representation s0, s1, s2)
    | MEMTYPE (s0, s1) ->
        MEMTYPE (Size.subst sigma_representation sigma_size s0, s1)
end

module Quantifier = struct
  type t =
    | Memory
    | Representation
    | Size
    | Type of Kind.t
  [@@deriving eq, ord, variants, sexp]

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
  [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    type t = Eqz [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
    [@@deriving eq, ord, variants, sexp]

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
  [@@deriving eq, ord, variants, sexp]

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
  [@@deriving eq, ord, variants, sexp]

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
  [@@deriving eq, ord, variants, sexp]

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
    | Variant of t list
    | Prod of t list
    | Struct of t list
    | Ref of Memory.t * t
    | CodeRef of FunctionType.t
    | Ser of t
    | Plug of Representation.t
    | Span of Size.t
    | Rec of Kind.t * t
    | Exists of Quantifier.t * t
  [@@deriving eq, ord, variants, sexp]

  (* val subst : (int -> Memory.t) -> (int -> Representation.t) -> (int -> Size.t) -> (int -> Type.t) -> t *)
  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
  val up_memory : ('a -> t) -> 'a -> t
  val up_representation : ('a -> t) -> 'a -> t
  val up_size : ('a -> t) -> 'a -> t
  val up_type : (int -> t) -> int -> t

  val ren :
    (int -> int) -> (int -> int) -> (int -> int) -> (int -> int) -> t -> t

  val subst :
    (int -> Memory.t) ->
    (int -> Representation.t) ->
    (int -> Size.t) ->
    (int -> t) ->
    t ->
    t
end = struct
  type t =
    | Var of int
    | I31
    | Num of NumType.t
    | Sum of t list
    | Variant of t list
    | Prod of t list
    | Struct of t list
    | Ref of Memory.t * t
    | CodeRef of FunctionType.t
    | Ser of t
    | Plug of Representation.t
    | Span of Size.t
    | Rec of Kind.t * t
    | Exists of Quantifier.t * t
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff : t -> unit = function
    | Var i -> fprintf ff "@[<2>(var %a)@]" Base.Int.pp i
    | I31 -> fprintf ff "i31"
    | Num nt -> fprintf ff "%a" NumType.pp nt
    | Sum ts ->
        fprintf ff "@[<2>(sum";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Variant ts ->
        fprintf ff "@[<2>(variant";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Prod ts ->
        fprintf ff "@[<2>(prod";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Struct ts ->
        fprintf ff "@[<2>(struct";
        List.iter ~f:(fprintf ff "@ %a" pp) ts;
        fprintf ff ")@]"
    | Ref (m, t) -> fprintf ff "@[<2>(ref@ %a@ %a)@]" Memory.pp m pp t
    | CodeRef ft -> fprintf ff "@[<2>(coderef@ %a)@]" FunctionType.pp ft
    | Ser t -> fprintf ff "@[<2>(ser@ %a)@]" pp t
    | Plug r -> fprintf ff "@[<2>(plug@ %a)@]" Representation.pp r
    | Span s -> fprintf ff "@[<2>(span@ %a)@]" Size.pp s
    | Rec (kind, t) -> fprintf ff "@[<2>(rec@ %a@ %a)@]" Kind.pp kind pp t
    | Exists (q, t) -> fprintf ff "@[<2>(exists@ %a@ %a)@]" Quantifier.pp q pp t

  open Unscoped

  let rec ren xi_memory xi_representation xi_size xi_type = function
    | Var s0 -> Var (xi_type s0)
    | I31 -> I31
    | Num s1 -> Num s1
    | Sum s1 -> Sum (map (ren xi_memory xi_representation xi_size xi_type) s1)
    | Variant s1 -> Variant (map (ren xi_memory xi_representation xi_size xi_type) s1)
    | Prod s1 -> Prod (map (ren xi_memory xi_representation xi_size xi_type) s1)
    | Struct s1 -> Struct (map (ren xi_memory xi_representation xi_size xi_type) s1)
    | Ref (s1, s2) -> Ref (Memory.ren xi_memory s1, ren xi_memory xi_representation xi_size xi_type s2)
    | CodeRef s1 -> CodeRef (FunctionType.ren xi_memory xi_representation xi_size xi_type s1)
    | Ser s0 -> Ser (ren xi_memory xi_representation xi_size xi_type s0)
    | Plug s1 -> Plug (Representation.ren xi_representation s1)
    | Span s1 -> Span (Size.ren xi_representation xi_size s1)
    | Rec (s0, s1) ->
        Rec (Kind.ren xi_representation xi_size s0,
             ren xi_memory xi_representation xi_size (up_ren xi_type) s1)
    | Exists (Memory, s1) ->
        Exists (Memory, ren (up_ren xi_memory) xi_representation xi_size xi_type s1)
    | Exists (Representation, s1) ->
        Exists (Representation, ren xi_memory (up_ren xi_representation) xi_size xi_type s1)
    | Exists (Size, s1) ->
        Exists (Size, ren xi_memory xi_representation (up_ren xi_size) xi_type s1)
    | Exists (Type s1, s2) ->
        Exists (Type (Kind.ren xi_representation xi_size s1),
                ren xi_memory xi_representation xi_size (up_ren xi_type) s2)
    [@@ocamlformat "disable"]

  let up_memory sigma = funcomp (ren shift id id id) sigma
  let up_representation sigma = funcomp (ren id id shift id) sigma
  let up_size sigma = funcomp (ren id id shift id) sigma
  let up_type sigma = scons (Var var_zero) (funcomp (ren id id id shift) sigma)

  let rec subst sigma_memory sigma_representation sigma_size sigma_type = function
    | Var s0 -> sigma_type s0
    | I31 -> I31
    | Num s1 -> Num s1
    | Sum s1 -> Sum (map (subst sigma_memory sigma_representation sigma_size sigma_type) s1)
    | Variant s1 -> Variant (map (subst sigma_memory sigma_representation sigma_size sigma_type) s1)
    | Prod s1 -> Prod (map (subst sigma_memory sigma_representation sigma_size sigma_type) s1)
    | Struct s1 -> Struct (map (subst sigma_memory sigma_representation sigma_size sigma_type) s1)
    | Ref (s1, s2) -> Ref (Memory.subst sigma_memory s1, subst sigma_memory sigma_representation sigma_size sigma_type s2)
    | CodeRef s1 -> CodeRef (FunctionType.subst sigma_memory sigma_representation sigma_size sigma_type s1)
    | Ser s0 -> Ser (subst sigma_memory sigma_representation sigma_size sigma_type s0)
    | Plug s1 -> Plug (Representation.subst sigma_representation s1)
    | Span s1 -> Span (Size.subst sigma_representation sigma_size s1)
    | Rec (s0, s1) ->
        Rec (Kind.subst sigma_representation sigma_size s0,
             subst
               (Memory.up_type sigma_memory) (Representation.up_type sigma_representation)
               (Size.up_type sigma_size) (up_type sigma_type) s1)
    | Exists (Memory, s1) ->
        Exists (Memory,
                subst
                  (Memory.up_memory sigma_memory) (Representation.up_memory sigma_representation)
                  (Size.up_memory sigma_size) (up_memory sigma_type) s1)
    | Exists (Representation, s1) ->
        Exists (Representation,
                subst
                  (Memory.up_representation sigma_memory) (Representation.up_representation sigma_representation)
                  (Size.up_representation sigma_size) (up_representation sigma_type) s1)
    | Exists (Size, s1) ->
        Exists (Size,
                subst
                  (Memory.up_size sigma_memory) (Representation.up_size sigma_representation)
                  (Size.up_size sigma_size) (up_size sigma_type) s1)
    | Exists (Type s1, s2) ->
        Exists (Type (Kind.subst sigma_representation sigma_size s1),
                subst
                  (Memory.up_type sigma_memory) (Representation.up_type sigma_representation)
                  (Size.up_type sigma_size) (up_type sigma_type) s2)
    [@@ocamlformat "disable"]
end

and FunctionType : sig
  type t = FunctionType of Quantifier.t list * Type.t list * Type.t list
  [@@deriving eq, ord, sexp]

  val ren :
    (int -> int) -> (int -> int) -> (int -> int) -> (int -> int) -> t -> t

  val subst :
    (int -> Memory.t) ->
    (int -> Representation.t) ->
    (int -> Size.t) ->
    (int -> Type.t) ->
    t ->
    t

  val pp_sexp : formatter -> t -> unit
  val pp : formatter -> t -> unit
end = struct
  type t = FunctionType of Quantifier.t list * Type.t list * Type.t list
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff (FunctionType (quals, ts1, ts2)) =
    let rec go ?(top = false) = function
      | [] ->
          if top then fprintf ff "@[(";
          List.iter ~f:(fprintf ff "%a@ " Type.pp) ts1;
          fprintf ff "->";
          List.iter ~f:(fprintf ff "@ %a" Type.pp) ts2;
          if top then fprintf ff ")@]"
      | x :: xs ->
          fprintf ff "@[(forall.%a" Quantifier.pp x;
          go xs;
          fprintf ff ")@]"
    in
    go ~top:true quals

  open Unscoped

  let ren xi_memory xi_representation xi_size xi_type ft =
    let (FunctionType (qs, s0, s1)) = ft in
    let rec go acc xi_memory xi_representation xi_size xi_type :
        Quantifier.t list -> t = function
      | [] ->
          FunctionType
            ( List.rev acc,
              List.map ~f:(Type.ren xi_memory xi_representation xi_size xi_type) s0,
              List.map ~f:(Type.ren xi_memory xi_representation xi_size xi_type) s1 )
      | Memory :: xs ->
          go (Memory :: acc) (up_ren xi_memory) xi_representation xi_size xi_type xs
      | Representation :: xs ->
          go (Representation :: acc) xi_memory (up_ren xi_representation) xi_size xi_type xs
      | Size :: xs ->
          go (Size :: acc) xi_memory xi_representation (up_ren xi_size) xi_type xs
      | Type k :: xs ->
          go (Type (Kind.ren xi_representation xi_size k) :: acc)
            xi_memory xi_representation xi_size (up_ren xi_type) xs
    in
    go [] xi_memory xi_representation xi_size xi_type qs
    [@@ocamlformat "disable"]

  let subst sigma_memory sigma_representation sigma_size sigma_type ft =
    let (FunctionType (qs, s0, s1)) = ft in
    let rec go acc sigma_memory sigma_representation sigma_size sigma_type :
        Quantifier.t list -> t = function
      | [] ->
          FunctionType
            ( List.rev acc,
              List.map ~f:(Type.subst sigma_memory sigma_representation sigma_size sigma_type) s0,
              List.map ~f:(Type.subst sigma_memory sigma_representation sigma_size sigma_type) s1 )
      | Memory :: xs ->
          go (Memory :: acc)
            (Memory.up_memory sigma_memory) (Representation.up_memory sigma_representation)
            (Size.up_memory sigma_size) (Type.up_memory sigma_type) xs
      | Representation :: xs ->
          go (Representation :: acc)
            (Memory.up_representation sigma_memory) (Representation.up_representation sigma_representation)
            (Size.up_representation sigma_size) (Type.up_representation sigma_type) xs
      | Size :: xs ->
          go (Size :: acc)
            (Memory.up_size sigma_memory) (Representation.up_size sigma_representation)
            (Size.up_size sigma_size) (Type.up_size sigma_type) xs
      | Type k :: xs ->
          go (Type (Kind.subst sigma_representation sigma_size k) :: acc)
            (Memory.up_type sigma_memory) (Representation.up_type sigma_representation)
            (Size.up_type sigma_size) (Type.up_type sigma_type) xs
    in
    go [] sigma_memory sigma_representation sigma_size sigma_type qs
    [@@ocamlformat "disable"]
end

module BlockType = struct
  type t =
    | ValType of Type.t list
    | ArrowType of int * Type.t list
  [@@deriving eq, ord, variants, sexp]

  let pp ff : t -> unit = function
    | ValType res ->
        fprintf ff "(@[result";
        List.iter ~f:(fprintf ff "@ %a" Type.pp) res;
        fprintf ff "@])"
    | ArrowType (inputs, res) ->
        fprintf ff "@[(";
        fprintf ff "<%a>@ " Base.Int.pp inputs;
        fprintf ff "->";
        List.iter ~f:(fprintf ff "@ %a" Type.pp) res;
        fprintf ff ")@]"
end

module LocalFx = struct
  type t =
    | LocalFx of (int * Type.t) list
    | InferFx
  [@@deriving eq, ord, variants, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Index = struct
  type t =
    | Mem of Memory.t
    | Rep of Representation.t
    | Size of Size.t
    | Type of Type.t
  [@@deriving eq, ord, variants, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Path = struct
  type t = Path of int list
  [@@deriving eq, ord, variants, sexp, show { with_path = false }]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Consume = struct
  type t =
    | Follow
    | Copy
    | Move
  [@@deriving eq, ord, variants, sexp]

  let pp ff : t -> unit = function
    | Follow -> fprintf ff "follow"
    | Copy -> fprintf ff "copy"
    | Move -> fprintf ff "move"
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
    | LocalGet of int * Consume.t
    | LocalSet of int
    | CodeRef of int
    | Inst of Index.t
    | Call of int * Index.t list
    | CallIndirect
    | Inject of int * Type.t list
    | InjectNew of BaseMemory.t * int * Type.t list
    | Case of BlockType.t * LocalFx.t * t list list
    | CaseLoad of BlockType.t * Consume.t * LocalFx.t * t list list
    | Group of int
    | Ungroup
    | Fold of Type.t
    | Unfold
    | Pack of Index.t * Type.t
    | Unpack of BlockType.t * LocalFx.t * t list
    | Tag
    | Untag
    | Cast of Type.t
    | New of BaseMemory.t
    | Load of Path.t * Consume.t
    | Store of Path.t
    | Swap of Path.t
  [@@deriving eq, ord, variants, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let rec pp ff : t -> unit =
    let pp_instrs ff (instrs : t list) =
      List.iteri
        ~f:(fun i -> if i = 0 then fprintf ff "%a" pp else fprintf ff "@,%a" pp)
        instrs
    in
    let pp_int = Base.Int.pp in
    function
    | Nop -> fprintf ff "nop"
    | Unreachable -> fprintf ff "unreachable"
    | Copy -> fprintf ff "copy"
    | Drop -> fprintf ff "drop"
    | Num ni -> fprintf ff "%a" NumInstruction.pp ni
    | NumConst (t, n) -> fprintf ff "%a.const %a" NumType.pp t pp_int n
    | Block (bt, lfx, instrs) ->
        fprintf ff "@[<v 0>@[<2>block@ %a@ %a@]@,@[<v 2>  %a@]@,end@]"
          BlockType.pp bt LocalFx.pp lfx pp_instrs instrs
    | Loop (bt, instrs) ->
        fprintf ff "@[<v 0>@[<2>loop@ %a@]@,@[<v 2>  %a@]@,end@]" BlockType.pp
          bt pp_instrs instrs
    | Ite (bt, lfx, e_thn, e_els) ->
        fprintf ff
          "@[<v 0>@[<2>if@ %a@ %a@]@,@[<v 2>  %a@]@,else@,@[<v 2>  %a@]@,end@]"
          BlockType.pp bt LocalFx.pp lfx pp_instrs e_thn pp_instrs e_els
    | Br i -> fprintf ff "@[<2>br@ %a@]" pp_int i
    | Return -> fprintf ff "return"
    | LocalGet (i, c) ->
        fprintf ff "@[<2>local.get@ %a@ %a@]" pp_int i Consume.pp c
    | LocalSet i -> fprintf ff "@[<2>local.set@ %a@]" pp_int i
    | CodeRef i -> fprintf ff "@[<2>coderef@ %a@]" pp_int i
    | Inst idx -> fprintf ff "@[<2>inst@ %a@]" Index.pp idx
    | Call (i, idxs) ->
        fprintf ff "@[<2>call@ %a" pp_int i;
        List.iter ~f:(fprintf ff "@ %a" Index.pp) idxs;
        fprintf ff "@]"
    | CallIndirect -> fprintf ff "call_indirect"
    | Inject (i, typs) ->
        fprintf ff "@[<2>inject@ %a" pp_int i;
        List.iter ~f:(fprintf ff " %a" Type.pp) typs;
        fprintf ff "@]"
    | InjectNew (mem, i, typs) ->
        fprintf ff "@[<2>inject_new@ %a@ %a" BaseMemory.pp mem pp_int i;
        List.iter ~f:(fprintf ff " %a" Type.pp) typs;
        fprintf ff "@]"
    | Case (bt, lfx, cases) ->
        fprintf ff "@[<v 0>@[<2>case@ %a@ %a@]@,@[<v 2>  " BlockType.pp bt
          LocalFx.pp lfx;
        List.iteri
          ~f:(fun i instrs ->
            if i <> 0 then fprintf ff "@,";
            fprintf ff "@[<v 2>(%a@,%a)@]" pp_int i pp_instrs instrs)
          cases;
        fprintf ff "@]@,end@]"
    | CaseLoad (bt, consume, lfx, cases) ->
        fprintf ff "@[<v 0>@[<2>case_load@ %a@ %a@ %a@]@,@[<v 2>  " BlockType.pp
          bt Consume.pp consume LocalFx.pp lfx;
        List.iteri
          ~f:(fun i instrs ->
            if i <> 0 then fprintf ff "@,";
            fprintf ff "@[<v 2>(%a@,%a)@]" pp_int i pp_instrs instrs)
          cases;
        fprintf ff "@]@,end@]"
    | Group i -> fprintf ff "@[<2>group@ %a@]" pp_int i
    | Ungroup -> fprintf ff "ungroup"
    | Fold t -> fprintf ff "@[<2>fold@ %a@]" Type.pp t
    | Unfold -> fprintf ff "unfold"
    | Pack (idx, t) -> fprintf ff "@[<2>pack@ %a@ %a@]" Index.pp idx Type.pp t
    | Unpack (bt, lfx, instrs) ->
        fprintf ff "@[<v 0>@[<2>unpack@ %a@ %a@]@,@[<v 2>  %a@]@,end@]"
          BlockType.pp bt LocalFx.pp lfx pp_instrs instrs
    | Tag -> fprintf ff "tag"
    | Untag -> fprintf ff "untag"
    | Cast t -> fprintf ff "@[<2>cast@ %a@]" Type.pp t
    | New m -> fprintf ff "@[<2>new@ %a@]" BaseMemory.pp m
    | Load (p, c) -> fprintf ff "@[<2>load@ %a@ %a@]" Path.pp p Consume.pp c
    | Store p -> fprintf ff "@[<2>store@ %a@]" Path.pp p
    | Swap p -> fprintf ff "@[<2>swap@ %a@]" Path.pp p
end

module Module = struct
  module Function = struct
    type t = {
      typ : FunctionType.t;
      locals : Representation.t list;
      body : Instruction.t list;
    }
    [@@deriving eq, ord, make, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff ({ typ; locals; body } : t) : unit =
      fprintf ff "@[<v 2>@[<4>(func@ %a" FunctionType.pp typ;
      if not @@ List.is_empty locals then (
        fprintf ff "@ (local";
        List.iter ~f:(fprintf ff "@ %a" Representation.pp) locals;
        fprintf ff ")");
      fprintf ff "@]";
      List.iter ~f:(fprintf ff "@,%a" Instruction.pp) body;
      fprintf ff ")@]"
  end

  module Export = struct
    module Desc = struct
      type t = Func of int [@@deriving eq, ord, variants, sexp]

      let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

      let pp ff : t -> unit = function
        | Func funcidx -> fprintf ff "(@[func %a@])" Base.Int.pp funcidx
    end

    type t = {
      name : string;
      desc : Desc.t;
    }
    [@@deriving eq, ord, make, sexp]

    let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let pp ff ({ name; desc } : t) : unit =
      fprintf ff "(@[export %a@ %a@])" String.pp name Desc.pp desc
  end

  type t = {
    imports : FunctionType.t list;
    functions : Function.t list;
    table : int list;
    exports : Export.t list;
  }
  [@@deriving eq, ord, make, sexp]

  let pp_sexp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let pp ff ({ imports; functions; table; exports } : t) : unit =
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
    print_sep
      ~f:(fprintf ff "(import %a" FunctionType.pp)
      ~sep:break_hint imports;
    print_sep ~f:(Function.pp ff) ~sep:break_hint functions;
    fprintf ff "@;@[(table@[<hv 2>";
    print_sep ~f:(Base.Int.pp ff) ~sep:space_hint table;
    fprintf ff "@])@]";
    print_sep ~f:(Export.pp ff) ~sep:break_hint exports;
    fprintf ff "@])@]"
end
