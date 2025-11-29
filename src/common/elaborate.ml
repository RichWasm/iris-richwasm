open! Base
open! Monads
open Stdlib.Format
module A = Syntax
module B = Annotated_syntax

module Env = struct
  type t = {
    local_offset : int;
    kinds : A.Kind.t list;
    labels : A.Type.t list list;
    return : A.Type.t list;
    functions : A.FunctionType.t list;
    table : A.FunctionType.t list;
    lfx : A.LocalFx.t Option.t;
  }
  [@@deriving make, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module State = struct
  type t = {
    locals : A.Type.t list;
    stack : A.Type.t list;
  }
  [@@deriving make, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Err = struct
  type kind_ctx =
    [ `Type of B.Type.t
    | `TypeA of A.Type.t
    | `Kind of B.Kind.t
    ]
  [@@deriving sexp]

  type wrap_ctx =
    [ `InstrTIn of A.Type.t list
    | `InstrTOut of A.Type.t list
    | `ElabTyp of A.Type.t
    | `HandleBT of A.BlockType.t
    | `HandleNewLocals of Env.t * A.Type.t list
    | `ElabTypElabKinds of B.Type.typ list
    ]
  [@@deriving sexp]

  type t =
    | TODO of string
    | InternalErr of string
    | InvalidLocalFx of (int * (int * A.Type.t) list)
    | TVarNotInEnv of (int * A.Kind.t list)
    | PopEmptyStack of string
    | ExpectedEqStack of (string * A.Type.t * A.Type.t)
    | InvalidLabel of int
    | UnexpectedPlugLocal of int * A.Representation.t
    | InvalidLocalIdx of (int * [ `Set | `Get | `Reset ])
    | CannotCopyNonCopyable
    | InvalidTableIdx of int
    | InvalidTableIdxModule of int
    | InstNonCoderef of A.Type.t
    | InvalidFunctionIdx of int
    | CallNotFullyInstanciated of A.FunctionType.t
    | ExpectedVALTYPE of string * kind_ctx
    | ExpectedMEMTYPE of string * kind_ctx
    | CannotMeet of string * B.Kind.t
    | ExpectedUnqualidfiedCoderef of A.Type.t
    | UngroupNonProd of A.Type.t
    | FoldNonRec of A.Type.t
    | UnfoldNonRec of A.Type.t
    | NonRef of [ `Load | `Store | `Swap ] * A.Type.t
    | LoadRefNonSer of A.Type.t
    | FunctionParamMustBeMonoRep
    | CannotResolvePath of
        [ `ExpectedStruct | `OutOfBounds ] * A.Path.t * A.Type.t
    | UnpackExpectsExists of A.Type.t
    | PackMismatch of A.Type.t * A.Type.t
    | IncorrectLocalFx of String.t * Int.t * A.Type.t List.t * A.Type.t List.t
    | LfxInvalidIndex of int * A.Type.t List.t
    | CannotInferLfx of
        [ `Ite of int * A.Type.t List.t * A.Type.t List.t
        | `Case of int * int * A.Type.t List.t * A.Type.t List.t
        ]
    | NonTrivialLfxInfer of [ `Unreachable | `Br | `Return ]
    | InstrErr of {
        error : t;
        instr : A.Instruction.t;
        env : Env.t;
        state : State.t;
      }
    | BlockErr of {
        error : t;
        instr : A.Instruction.t;
        env : Env.t;
        state : State.t;
      }
    | Ctx of {
        error : t;
        ctx : wrap_ctx;
      }
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = ResultM (Err)
open Res

let wrap_result ctx = function
  | Ok x -> Ok x
  | Error error -> Error (Err.Ctx { error; ctx })

let elab_copyability : A.Copyability.t -> B.Copyability.t = function
  | NoCopy -> NoCopy
  | ImCopy -> ImCopy
  | ExCopy -> ExCopy

let elab_dropability : A.Dropability.t -> B.Dropability.t = function
  | ImDrop -> ImDrop
  | ExDrop -> ExDrop

let elab_base_memory : A.BaseMemory.t -> B.BaseMemory.t = function
  | MM -> MemMM
  | GC -> MemGC

let elab_memory : A.Memory.t -> B.Memory.t = function
  | Var x -> VarM (Z.of_int x)
  | Base m -> BaseM (elab_base_memory m)

let elab_atomic_rep : A.AtomicRep.t -> B.AtomicRep.t = function
  | Ptr -> PtrR
  | I32 -> I32R
  | I64 -> I64R
  | F32 -> F32R
  | F64 -> F64R

let rec elab_representation : A.Representation.t -> B.Representation.t =
  function
  | Var x -> VarR (Z.of_int x)
  | Sum reps -> SumR (List.map ~f:elab_representation reps)
  | Prod reps -> ProdR (List.map ~f:elab_representation reps)
  | Atom rep -> AtomR (elab_atomic_rep rep)

let rec elab_size : A.Size.t -> B.Size.t = function
  | Var x -> VarS (Z.of_int x)
  | Sum sizes -> SumS (List.map ~f:elab_size sizes)
  | Prod sizes -> ProdS (List.map ~f:elab_size sizes)
  | Rep rep -> RepS (elab_representation rep)
  | Const s -> ConstS (Z.of_int s)

let elab_kind : A.Kind.t -> B.Kind.t = function
  | VALTYPE (representation, copyability, dropability) ->
      VALTYPE
        ( elab_representation representation,
          elab_copyability copyability,
          elab_dropability dropability )
  | MEMTYPE (size, dropability) ->
      MEMTYPE (elab_size size, elab_dropability dropability)

let unelab_copyability : B.Copyability.t -> A.Copyability.t = function
  | NoCopy -> NoCopy
  | ImCopy -> ImCopy
  | ExCopy -> ExCopy

let unelab_dropability : B.Dropability.t -> A.Dropability.t = function
  | ImDrop -> ImDrop
  | ExDrop -> ExDrop

let unelab_base_memory : B.BaseMemory.t -> A.BaseMemory.t = function
  | MemMM -> MM
  | MemGC -> GC

let unelab_memory : B.Memory.t -> A.Memory.t = function
  | VarM x -> Var (Z.to_int x)
  | BaseM m -> Base (unelab_base_memory m)

let unelab_atomic_rep : B.AtomicRep.t -> A.AtomicRep.t = function
  | PtrR -> Ptr
  | I32R -> I32
  | I64R -> I64
  | F32R -> F32
  | F64R -> F64

let rec unelab_representation : B.Representation.t -> A.Representation.t =
  function
  | VarR x -> Var (Z.to_int x)
  | SumR reps -> Sum (List.map ~f:unelab_representation reps)
  | ProdR reps -> Prod (List.map ~f:unelab_representation reps)
  | AtomR rep -> Atom (unelab_atomic_rep rep)

let rec unelab_size : B.Size.t -> A.Size.t = function
  | VarS x -> Var (Z.to_int x)
  | SumS sizes -> Sum (List.map ~f:unelab_size sizes)
  | ProdS sizes -> Prod (List.map ~f:unelab_size sizes)
  | RepS rep -> Rep (unelab_representation rep)
  | ConstS s -> Const (Z.to_int s)

let unelab_kind : B.Kind.t -> A.Kind.t = function
  | VALTYPE (representation, copyability, dropability) ->
      VALTYPE
        ( unelab_representation representation,
          unelab_copyability copyability,
          unelab_dropability dropability )
  | MEMTYPE (size, dropability) ->
      MEMTYPE (unelab_size size, unelab_dropability dropability)

let elab_sign : A.Sign.t -> B.Sign.t = function
  | Unsigned -> SignU
  | Signed -> SignS

let elab_int_type : A.Int.Type.t -> B.Int.Type.t = function
  | I32 -> I32T
  | I64 -> I64T

let elab_int_unop : A.Int.Unop.t -> B.Int.Unop.t = function
  | Clz -> ClzI
  | Ctz -> CtzI
  | Popcnt -> PopcntI

let elab_int_binop : A.Int.Binop.t -> B.Int.Binop.t = function
  | Add -> AddI
  | Sub -> SubI
  | Mul -> MulI
  | Div sign -> DivI (elab_sign sign)
  | Rem sign -> RemI (elab_sign sign)
  | And -> AndI
  | Or -> OrI
  | Xor -> XorI
  | Shl -> ShlI
  | Shr sign -> ShrI (elab_sign sign)
  | Rotl -> RotlI
  | Rotr -> RotrI

let elab_int_testop : A.Int.Testop.t -> B.Int.Testop.t = function
  | Eqz -> EqzI

let elab_int_replop : A.Int.Relop.t -> B.Int.Relop.t = function
  | Eq -> EqI
  | Ne -> NeI
  | Lt sign -> LtI (elab_sign sign)
  | Gt sign -> GtI (elab_sign sign)
  | Le sign -> LeI (elab_sign sign)
  | Ge sign -> GeI (elab_sign sign)

let elab_float_type : A.Float.Type.t -> B.Float.Type.t = function
  | F32 -> F32T
  | F64 -> F64T

let elab_float_unop : A.Float.Unop.t -> B.Float.Unop.t = function
  | Neg -> NegF
  | Abs -> AbsF
  | Ceil -> CeilF
  | Floor -> FloorF
  | Trunc -> TruncF
  | Nearest -> NearestF
  | Sqrt -> SqrtF

let elab_float_binop : A.Float.Binop.t -> B.Float.Binop.t = function
  | Add -> AddF
  | Sub -> SubF
  | Mul -> MulF
  | Div -> DivF
  | Min -> MinF
  | Max -> MaxF
  | CopySign -> CopySignF

let elab_float_relop : A.Float.Relop.t -> B.Float.Relop.t = function
  | Eq -> EqF
  | Ne -> NeF
  | Lt -> LtF
  | Gt -> GtF
  | Le -> LeF
  | Ge -> GeF

let elab_num_type : A.NumType.t -> B.NumType.t = function
  | Int int_type -> IntT (elab_int_type int_type)
  | Float float_type -> FloatT (elab_float_type float_type)

let elab_conversion_op : A.ConversionOp.t -> B.ConversionOp.t = function
  | Wrap -> CWrap
  | Extend sign -> CExtend (elab_sign sign)
  | Trunc (ft, it, sign) ->
      CTrunc (elab_float_type ft, elab_int_type it, elab_sign sign)
  | Demote -> CDemote
  | Promote -> CPromote
  | Convert (it, ft, sign) ->
      CConvert (elab_int_type it, elab_float_type ft, elab_sign sign)
  | Reinterpret num_type -> CReinterpret (elab_num_type num_type)

let kind_of_typ (env : 'a list) : B.Type.t -> B.Kind.t t = function
  | VarT x ->
      let i = Z.to_int x in
      List.nth env i |> lift_option (TVarNotInEnv (i, env)) >>| elab_kind
  | I31T k
  | NumT (k, _)
  | SumT (k, _)
  | VariantT (k, _)
  | ProdT (k, _)
  | StructT (k, _)
  | RefT (k, _, _)
  | CodeRefT (k, _)
  | SerT (k, _)
  | PlugT (k, _)
  | SpanT (k, _)
  | RecT (k, _)
  | ExistsMemT (k, _)
  | ExistsRepT (k, _)
  | ExistsSizeT (k, _)
  | ExistsTypeT (k, _, _) -> ret k

let meet_valtypes
    (combine_rep : B.Representation.t list -> B.Representation.t)
    (kinds : B.Kind.t list) : B.Kind.t t =
  let rec go reps copy drop : B.Kind.t list -> B.Kind.t t =
    let open B in
    function
    | [] -> Kind.VALTYPE (combine_rep (List.rev reps), copy, drop) |> ret
    | VALTYPE (rep, copy', drop') :: xs ->
        go (rep :: reps)
          (Copyability.meet copy copy')
          (Dropability.meet drop drop')
          xs
    | x :: _ -> fail (CannotMeet ("expected valtype", x))
  in
  go [] ImCopy ImDrop kinds

let meet_memtypes
    (combine_sizes : B.Size.t list -> B.Size.t)
    (kinds : B.Kind.t list) : B.Kind.t t =
  let rec go sizes drop : B.Kind.t list -> B.Kind.t t =
    let open B in
    function
    | [] -> Kind.MEMTYPE (combine_sizes (List.rev sizes), drop) |> ret
    | MEMTYPE (size, drop') :: xs ->
        go (size :: sizes) (Dropability.meet drop drop') xs
    | x :: _ -> fail (CannotMeet ("expected memtype", x))
  in
  go [] ImDrop kinds

(* TODO: this needs to be double checked *)
let rec elab_type (env : A.Kind.t list) : A.Type.t -> B.Type.t t =
  let rep_of_nt : A.NumType.t -> B.AtomicRep.t = function
    | Int I32 -> I32R
    | Int I64 -> I64R
    | Float F32 -> F32R
    | Float F64 -> F64R
  in
  let sumR x = B.Representation.SumR x in
  let prodR x = B.Representation.ProdR x in
  let sumS x = B.Size.SumS x in
  let prodS x = B.Size.ProdS x in
  let unshift n =
    if Z.equal n Z.zero then
      failwith "Cannot strengthen zero"
    else
      Z.sub Z.one n
  in
  let id x = x in

  let elab_kinds ts' =
    mapM ~f:(kind_of_typ env) ts' |> wrap_result (`ElabTypElabKinds ts')
  in

  let open B.Type in
  function
  | Var x -> ret @@ VarT (Z.of_int x)
  | I31 -> ret @@ I31T (VALTYPE (AtomR PtrR, ImCopy, ImDrop))
  | Num nt ->
      let+ () = ret () in
      NumT (VALTYPE (AtomR (rep_of_nt nt), ImCopy, ImDrop), elab_num_type nt)
  | Sum ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = elab_kinds ts' >>= meet_valtypes sumR in
      ret @@ SumT (k, ts')
  | Variant ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = elab_kinds ts' >>= meet_memtypes sumS in
      ret @@ VariantT (k, ts')
  | Prod ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = elab_kinds ts' >>= meet_valtypes prodR in
      ret @@ ProdT (k, ts')
  | Struct ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = elab_kinds ts' >>= meet_memtypes prodS in
      ret @@ StructT (k, ts')
  | Ref (Base MM, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (AtomR PtrR, NoCopy, ExDrop), BaseM MemMM, t')
  | Ref (Base GC, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (AtomR PtrR, ExCopy, ExDrop), BaseM MemGC, t')
  | Ref (mem, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (AtomR PtrR, NoCopy, ExDrop), elab_memory mem, t')
  | CodeRef ft ->
      let+ ft' = elab_function_type env ft in
      CodeRefT (VALTYPE (AtomR I32R, ImCopy, ImDrop), ft')
  | Ser t ->
      let* t' = elab_type env t in
      let* rep, dropability =
        kind_of_typ env t' >>= function
        | VALTYPE (rep, _, dropability) -> ret (rep, dropability)
        | _ -> fail (ExpectedVALTYPE ("Ser", `Type t'))
      in
      ret @@ SerT (MEMTYPE (RepS rep, dropability), t')
  | Plug rep ->
      let rep' = elab_representation rep in
      ret @@ PlugT (VALTYPE (rep', ImCopy, ImDrop), rep')
  | Span size ->
      let size' = elab_size size in
      ret @@ SpanT (MEMTYPE (size', ImDrop), size')
  | Rec (kind, t) ->
      let env' = kind :: env in
      let* t' = elab_type env' t in
      let* kind' = kind_of_typ env' t' in
      ret @@ RecT (kind', t')
  (* we only need to keep track of type variables,
     BUT the variables should not be present for the type's kind,
     so when we copy the kind from the inner type, we must unshift
     type variables appropriately--idx 0 must not be used *)
  | Exists (Memory, t) ->
      let* t' = elab_type env t in
      let* k = kind_of_typ env t' >>| B.Kind.ren id id in
      ret @@ ExistsMemT (k, t')
  | Exists (Representation, t) ->
      let* t' = elab_type env t in
      let* k = kind_of_typ env t' >>| B.Kind.ren unshift id in
      ret @@ ExistsMemT (k, t')
  | Exists (Size, t) ->
      let* t' = elab_type env t in
      let* k = kind_of_typ env t' >>| B.Kind.ren id unshift in
      ret @@ ExistsSizeT (k, t')
  | Exists (Type k, t) ->
      let env' = k :: env in
      let* t' = elab_type env' t in
      let k' = elab_kind k in
      let* kind = kind_of_typ env' t' in
      ret @@ ExistsTypeT (kind, k', t')

and elab_function_type
    (env : A.Kind.t list)
    (FunctionType (quals, input, output) : A.FunctionType.t) :
    B.FunctionType.t t =
  let env' =
    List.fold_left quals ~init:env ~f:(fun acc -> function
      | Memory | Representation | Size -> acc
      | Type k -> k :: acc)
  in
  let* input' = mapM ~f:(elab_type env') input in
  let* output' = mapM ~f:(elab_type env') output in

  let rec go : A.Quantifier.t list -> B.FunctionType.t = function
    | [] -> MonoFunT (input', output')
    | Memory :: xs -> ForallMemT (go xs)
    | Representation :: xs -> ForallRepT (go xs)
    | Size :: xs -> ForallSizeT (go xs)
    | Type kind :: xs -> ForallTypeT (elab_kind kind, go xs)
  in

  ret @@ go quals

let representation_of_typ (kinds : A.Kind.t list) t =
  kind_of_typ kinds t >>= function
  | VALTYPE (r, _, _) -> ret r
  | _ -> fail (ExpectedVALTYPE ("representation of ", `Type t))

let copyability_of_typ (kinds : A.Kind.t list) t =
  kind_of_typ kinds t >>= function
  | VALTYPE (_, c, _) -> ret c
  | _ -> fail (ExpectedVALTYPE ("copyability of", `Type t))

let size_of_typ (kinds : A.Kind.t list) t =
  kind_of_typ kinds t >>= function
  | MEMTYPE (sz, _) -> ret sz
  | _ -> fail (ExpectedMEMTYPE ("size of", `Type t))

module InstrM = struct
  include StateM (State) (Err)
  open A

  let push (t : Type.t) : unit t =
    modify (fun s -> { s with stack = t :: s.stack })

  let pop (ctx : string) : Type.t t =
    let* st = get in
    match st.stack with
    | [] -> fail (PopEmptyStack ctx)
    | top :: rst ->
        let+ () = put { st with stack = rst } in
        top

  let set_local (i : int) (t : Type.t) : unit t =
    let* st = get in
    let* () =
      fail_if (List.length st.locals <= i) (InvalidLocalIdx (i, `Set))
    in
    let locals' =
      List.mapi st.locals ~f:(fun i' x -> if i <> i' then x else t)
    in
    modify (fun st -> { st with locals = locals' })

  let reset_local (i : int) (env : Env.t) : unit t =
    let* st = get in
    let* () =
      fail_if (List.length st.locals <= i) (InvalidLocalIdx (i, `Reset))
    in
    let* locals' =
      mapiM st.locals ~f:(fun i' t ->
          if i <> i' then
            ret t
          else
            let* rep =
              Res.(
                elab_type env.kinds t
                >>= representation_of_typ env.kinds
                >>| unelab_representation)
              |> lift_result
            in
            ret @@ A.Type.Plug rep)
    in
    modify (fun st -> { st with locals = locals' })

  let wrap_ctx (ctx : Err.wrap_ctx) (v : 'a t) : 'a t =
   fun state -> wrap_result ctx (v state)

  let wrap_lift (ctx : Err.wrap_ctx) (r : 'a Res.t) : 'a t =
    lift_result r |> wrap_ctx ctx
end

(* The unannotated AST treats local effects as a diff between the current locals
   and the state of the locals after the block is run, while the annotated AST
   expects local effects to be the entire new state of the locals *)
let calculate_locals (locals : A.Type.t list) (fxs : (int * A.Type.t) list) :
    A.Type.t List.t Res.t =
  let locals_arr = Array.of_list locals in
  let+ () =
    iterM
      ~f:(fun (idx, t) ->
        try
          locals_arr.(idx) <- t;
          ret ()
        with _ -> fail (LfxInvalidIndex (idx, locals)))
      fxs
  in
  List.of_array locals_arr

let handle_new_locals (env : Env.t) (locals : A.Type.t list) =
  let open InstrM in
  let* () = modify (fun st -> { st with locals }) in
  let* locals' =
    Res.mapM ~f:(elab_type env.kinds) locals
    |> wrap_lift (`HandleNewLocals (env, locals))
  in
  ret locals'

let handle_local_fx (env : Env.t) (lfx : (int * A.Type.t) list) :
    B.Type.t List.t InstrM.t =
  let open InstrM in
  let* outer_st = get in
  let* locals = calculate_locals outer_st.locals lfx |> lift_result in
  handle_new_locals env locals

let compare_lfx f a b =
  let open InstrM in
  List.zip a b
  |> ( function
  | Ok l -> ret l
  | Unequal_lengths -> fail (InternalErr "locals length mismatch") )
  >>= iteriM ~f:(fun i (expected, actual) ->
      fail_ifn (A.Type.equal expected actual) (f i a b))

let verify_lfx (inner_st : State.t) (lfx : (int * A.Type.t) list) ctx :
    Unit.t InstrM.t =
  let open InstrM in
  let* outer_st = get in
  let actual_locals = inner_st.locals in
  let* expected_locals = calculate_locals outer_st.locals lfx |> lift_result in
  compare_lfx
    (fun i a b -> IncorrectLocalFx (ctx, i, a, b))
    expected_locals actual_locals

let elab_index (env : A.Kind.t list) : A.Index.t -> B.Index.t t =
  let open B.Index in
  function
  | Mem mem -> ret @@ MemI (elab_memory mem)
  | Rep rep -> ret @@ RepI (elab_representation rep)
  | Size size -> ret @@ SizeI (elab_size size)
  | Type typ -> elab_type env typ >>| fun t -> TypeI t

let elab_path (Path ns : A.Path.t) : Z.t list = List.map ~f:Z.of_int ns

let instr_t_of env t_in t_out : B.InstructionType.t InstrM.t =
  let open InstrM in
  let* t_in' = Res.mapM ~f:(elab_type env) t_in |> wrap_lift (`InstrTIn t_in) in
  let* t_out' =
    Res.mapM ~f:(elab_type env) t_out |> wrap_lift (`InstrTOut t_out)
  in
  ret @@ B.InstructionType.InstrT (t_in', t_out')

let mono_in_out (kenv : A.Kind.t list) ctx t_in t_out :
    B.InstructionType.t InstrM.t =
  let open InstrM in
  let* t_in' =
    List.rev t_in
    |> mapiM ~f:(fun i _ -> pop (sprintf "%s-In%i" ctx i))
    >>| List.rev
  in
  let* () =
    List.zip_exn t_in t_in'
    |> iteriM ~f:(fun i (a, b) ->
        fail_ifn (A.Type.equal a b)
          (ExpectedEqStack (sprintf "%s%i" ctx i, a, b)))
  in
  let* () = t_out |> iterM ~f:push in
  instr_t_of kenv t_in t_out

let elab_num_instruction (kenv : A.Kind.t list) :
    A.NumInstruction.t -> (B.InstructionType.t * B.NumInstruction.t) InstrM.t =
  let open InstrM in
  let open B.NumInstruction in
  function
  | Int1 (t, o) ->
      let* t_in = pop "Int1" in
      let* () = push t_in in
      let* it = instr_t_of kenv [ t_in ] [ t_in ] in
      let ni = IInt1 (elab_int_type t, elab_int_unop o) in
      ret (it, ni)
  | Int2 (t, o) ->
      let* t_in1 = pop "Int2-1" in
      let* t_in2 = pop "Int2-2" in
      let* () =
        fail_ifn (A.Type.equal t_in1 t_in2)
          (ExpectedEqStack ("Int2", t_in1, t_in2))
      in
      let* () = push t_in1 in
      let* it = instr_t_of kenv [ t_in2; t_in1 ] [ t_in1 ] in
      let ni = IInt2 (elab_int_type t, elab_int_binop o) in
      ret (it, ni)
  | IntTest (t, o) ->
      let* t_in = pop "IntTest" in
      let t_out : A.Type.t = Num (Int I32) in
      let* () = push t_out in
      let* it = instr_t_of kenv [ t_in ] [ t_out ] in
      let ni = IIntTest (elab_int_type t, elab_int_testop o) in
      ret (it, ni)
  | IntRel (t, o) ->
      let* t_in1 = pop "IntRel-1" in
      let* t_in2 = pop "IntRel-2" in
      let* () =
        fail_ifn (A.Type.equal t_in1 t_in2)
          (ExpectedEqStack ("IntRel", t_in1, t_in2))
      in
      let t_out : A.Type.t = Num (Int I32) in
      let* () = push t_out in
      let* it = instr_t_of kenv [ t_in2; t_in1 ] [ t_out ] in
      let ni = IIntRel (elab_int_type t, elab_int_replop o) in
      ret (it, ni)
  | Float1 (t, o) ->
      let* t_in = pop "Float1" in
      let* () = push t_in in
      let* it = instr_t_of kenv [ t_in ] [ t_in ] in
      let ni = IFloat1 (elab_float_type t, elab_float_unop o) in
      ret (it, ni)
  | Float2 (t, o) ->
      let* t_in1 = pop "Float2-1" in
      let* t_in2 = pop "Float2-2" in
      let* () =
        fail_ifn (A.Type.equal t_in1 t_in2)
          (ExpectedEqStack ("Float2", t_in1, t_in2))
      in
      let* () = push t_in1 in
      let* it = instr_t_of kenv [ t_in2; t_in1 ] [ t_in1 ] in
      let ni = IFloat2 (elab_float_type t, elab_float_binop o) in
      ret (it, ni)
  | FloatRel (t, o) ->
      let* t_in1 = pop "FloatRel-1" in
      let* t_in2 = pop "FloatRel-2" in
      let* () =
        fail_ifn (A.Type.equal t_in1 t_in2)
          (ExpectedEqStack ("FloatRel", t_in1, t_in2))
      in
      let t_out : A.Type.t = Num (Float F32) in
      let* () = push t_out in
      let* it = instr_t_of kenv [ t_in2; t_in1 ] [ t_out ] in
      let ni = IFloatRel (elab_float_type t, elab_float_relop o) in
      ret (it, ni)
  | Cvt Wrap ->
      let+ it =
        mono_in_out kenv "CvtWrap" [ Num (Int I64) ] [ Num (Int I32) ]
      in
      (it, ICvt CWrap)
  | Cvt (Extend sign) ->
      let+ it =
        mono_in_out kenv "CvtExtend" [ Num (Int I32) ] [ Num (Int I64) ]
      in
      (it, ICvt (CExtend (elab_sign sign)))
  | Cvt (Trunc (ft, ityp, sign)) ->
      let+ it =
        mono_in_out kenv "CvtTrunc" [ Num (Float ft) ] [ Num (Int ityp) ]
      in
      ( it,
        ICvt (CTrunc (elab_float_type ft, elab_int_type ityp, elab_sign sign))
      )
  | Cvt Demote ->
      let+ it =
        mono_in_out kenv "CvtDemote" [ Num (Float F64) ] [ Num (Float F32) ]
      in
      (it, ICvt CDemote)
  | Cvt Promote ->
      let+ it =
        mono_in_out kenv "CvtPromote" [ Num (Float F32) ] [ Num (Float F64) ]
      in
      (it, ICvt CPromote)
  | Cvt (Convert (ityp, ft, sign)) ->
      let+ it =
        mono_in_out kenv "CvtConvert" [ Num (Int ityp) ] [ Num (Float ft) ]
      in
      ( it,
        ICvt (CConvert (elab_int_type ityp, elab_float_type ft, elab_sign sign))
      )
  | Cvt (Reinterpret num_type) ->
      let* t_in = pop "CvtReinterpret" in
      let* () = push (Num num_type) in
      let* it = instr_t_of kenv [ t_in ] [ Num num_type ] in
      let ni = ICvt (CReinterpret (elab_num_type num_type)) in
      ret (it, ni)

module ASubst = struct
  include A.Unscoped
  module M = A.Memory
  module R = A.Representation
  module S = A.Size
  module T = A.Type
  module FT = A.FunctionType
end

let function_typ_inst (idx : A.Index.t) (ft : A.FunctionType.t) =
  let open ASubst in
  (match idx with
  | Mem mem -> FT.subst (scons mem M.var) R.var S.var T.var
  | Rep rep -> FT.subst M.var (scons rep R.var) S.var T.var
  | Size size -> FT.subst M.var R.var (scons size S.var) T.var
  | Type typ -> FT.subst M.var R.var S.var (scons typ T.var))
    ft

let function_typ_insts (idxs : A.Index.t list) (ft : A.FunctionType.t) =
  List.fold ~init:ft ~f:(fun ft idx -> function_typ_inst idx ft) idxs

let is_effective_move (consume : A.Consume.t) copyable =
  match consume with
  | Follow -> ret @@ not copyable
  | Copy -> if not copyable then fail CannotCopyNonCopyable else ret false
  | Move -> ret true

(* This is an executable version of what is found in typing.v but is for the
   unnanotated AST. *)

type path_result = {
  prefix : A.Type.t list;
  target : A.Type.t;
  replaced : A.Type.t;
}

let rec resolves_path
    (t : A.Type.t)
    (Path path : A.Path.t)
    (replacement : A.Type.t option) : path_result t =
  match (path, replacement) with
  | [], None -> ret { prefix = []; target = t; replaced = t }
  | [], Some t' -> ret { prefix = []; target = t; replaced = t' }
  | i :: p', _ ->
      (match t with
      | Struct ts ->
          let ts0, rest = List.split_n ts i in
          (match rest with
          | [] -> fail (CannotResolvePath (`OutOfBounds, Path path, t))
          | t_field :: ts' ->
              let+ pr = resolves_path t_field (Path p') replacement in
              {
                pr with
                prefix = ts0 @ pr.prefix;
                replaced = Struct (ts0 @ (pr.replaced :: ts'));
              })
      | _ -> fail (CannotResolvePath (`ExpectedStruct, Path path, t)))

(* /end *)

let[@warning "-27"] rec elab_instruction (env : Env.t) :
    A.Instruction.t -> B.Instruction.t InstrM.t =
  let open InstrM in
  let open B.Instruction in
  let handle_bt ?(lfx : A.LocalFx.t Option.t) (bt : A.BlockType.t) =
    let* init_st = get in
    let* consume, result =
      match bt with
      | ValType res -> ret ([], res)
      | ArrowType (num, res) ->
          List.init ~f:(fun x -> x) num
          |> List.rev
          |> mapM ~f:(fun i -> pop (sprintf "Block-n%i" i))
          >>| List.rev
          >>| fun x -> (x, res)
    in
    let+ () = iterM result ~f:push |> wrap_ctx (`HandleBT bt) in
    let env' =
      {
        env with
        labels = result :: env.labels;
        lfx =
          (match lfx with
          | Some lfx -> Some lfx
          | None -> env.lfx);
      }
    in
    let st_inner = { init_st with stack = consume } in
    (consume, result, env', st_inner)
  in
  let ( >>=^ ) m f = m >>= fun x -> f x |> lift_result in
  let ( >>^| ) r f = r |> Result.map ~f |> lift_result in
  let mapM_st ~f x st = mapM ~f x st |> lift_result in
  let elab_block env instrs st =
    mapM_st instrs
      ~f:(fun instr ->
        fun state ->
         let res = elab_instruction env instr state in
         match res with
         | Ok x -> Ok x
         | Error error -> Error (BlockErr { error; instr; env; state }))
      st
  in
  let have_to_infer_lfx =
    Option.value_map ~default:false ~f:A.LocalFx.is_inferfx env.lfx
  in
  function
  | Nop -> ret @@ INop (InstrT ([], []))
  | Unreachable ->
      let* () = fail_if have_to_infer_lfx (NonTrivialLfxInfer `Unreachable) in
      let* st = get in
      let* it = mono_in_out env.kinds "Unreachable" st.stack env.return in
      ret @@ IUnreachable it
  | Copy ->
      let* t = pop "Copy" in
      let* () = push t in
      let* () = push t in
      let* it = instr_t_of env.kinds [ t ] [ t; t ] in
      ret @@ ICopy it
  | Drop ->
      let* t = pop "Drop" in
      let* it = instr_t_of env.kinds [ t ] [] in
      ret @@ IDrop it
  | Num ni ->
      let* it, ni' = elab_num_instruction env.kinds ni in
      ret @@ INum (it, ni')
  | NumConst (nt, i) ->
      let* () = push (Num nt) in
      let* it = instr_t_of env.kinds [] [ Num nt ] in
      ret @@ INumConst (it, Z.of_int i)
  | Block (bt, lfx, instrs) ->
      let* consume, result, env', st_inner = handle_bt ~lfx bt in
      let* instrs', st' = elab_block env' instrs st_inner in
      let* lfx' =
        match lfx with
        | LocalFx lfx ->
            let* () = verify_lfx st' lfx "block" in
            handle_local_fx env lfx
        | InferFx -> handle_new_locals env st'.locals
      in
      let* it = instr_t_of env.kinds consume result in
      ret @@ IBlock (it, lfx', instrs')
  | Loop (bt, instrs) ->
      let* consume, result, env', st_inner = handle_bt bt in
      let* instrs', _ = elab_block env' instrs st_inner in
      let* it = instr_t_of env.kinds consume result in
      ret @@ ILoop (it, instrs')
  | Ite (bt, lfx, thn, els) ->
      let* consume, result, env', st_inner = handle_bt ~lfx bt in
      let* thn', thn_st = elab_block env' thn st_inner in
      let* els', els_st = elab_block env' els st_inner in
      let* lfx' =
        match lfx with
        | LocalFx lfx ->
            let* () = verify_lfx thn_st lfx "ite::thn" in
            let* () = verify_lfx els_st lfx "ite::els" in
            handle_local_fx env lfx
        | InferFx ->
            let* () =
              compare_lfx
                (fun i a b -> CannotInferLfx (`Ite (i, a, b)))
                thn_st.locals els_st.locals
            in
            handle_new_locals env thn_st.locals
      in
      let* it = instr_t_of env.kinds consume result in
      ret @@ IIte (it, lfx', thn', els')
  | Br label ->
      let* () = fail_if have_to_infer_lfx (NonTrivialLfxInfer `Br) in
      let* st = get in
      let* result =
        List.nth env.labels label |> lift_option (InvalidLabel label)
      in
      let* it = mono_in_out env.kinds "Br" st.stack result in
      ret @@ IBr (it, Z.of_int label)
  | Return ->
      let* () = fail_if have_to_infer_lfx (NonTrivialLfxInfer `Return) in
      let* st = get in
      let* it = mono_in_out env.kinds "Return" st.stack env.return in
      ret @@ IReturn it
  | LocalGet (i, consume) ->
      let* st = get in
      let* t =
        List.nth st.locals i |> lift_option (InvalidLocalIdx (i, `Get))
        (* NOTE: we don't *have* to error here but it makes debugging much easier *)
        (* >>= function
        | Plug rep -> fail (UnexpectedPlugLocal (i, rep))
        | x -> ret x *)
      in
      let* t' = lift_result @@ elab_type env.kinds t in
      let* im_copyable =
        copyability_of_typ env.kinds t' >>^| function
        | ImCopy -> true
        | _ -> false
      in
      let* should_move = is_effective_move consume im_copyable |> lift_result in
      let* () = if should_move then reset_local i env else ret () in
      let* it = mono_in_out env.kinds "LocalGet" [] [ t ] in
      ret @@ ILocalGet (it, Z.of_int i)
  | LocalSet i ->
      let* t = pop "LocalSet" in
      let* t' = lift_result @@ elab_type env.kinds t in
      let* () = set_local i t in
      ret @@ ILocalSet (InstrT ([], [ t' ]), Z.of_int i)
  | CodeRef i ->
      let* ft = List.nth env.table i |> lift_option (InvalidTableIdx i) in
      let* it = mono_in_out env.kinds "CodeRef" [] [ CodeRef ft ] in
      ret @@ ICodeRef (it, Z.of_int i)
  | Inst idx ->
      let* ft =
        pop "Inst" >>= function
        | CodeRef ft -> ret ft
        | x -> fail (InstNonCoderef x)
      in
      let ft' = function_typ_inst idx ft in
      let* it = instr_t_of env.kinds [ CodeRef ft ] [ CodeRef ft' ] in
      let* () = push (CodeRef ft') in
      let* idx' = elab_index env.kinds idx |> lift_result in
      ret @@ IInst (it, idx')
  | Call (i, idxs) ->
      let* idxs' = Res.mapM ~f:(elab_index env.kinds) idxs |> lift_result in
      let* ft =
        List.nth env.functions i |> lift_option (InvalidFunctionIdx i)
      in
      let* ts1, ts2 =
        match ft with
        | FunctionType ([], ts1, ts2) -> ret (ts1, ts2)
        | x -> fail (CallNotFullyInstanciated x)
      in
      let* it = mono_in_out env.kinds "Call" ts1 ts2 in
      ret @@ ICall (it, Z.of_int i, idxs')
  | CallIndirect ->
      let* ts1, ts2 =
        pop "CallIndirect" >>= function
        | CodeRef (FunctionType ([], ts1, ts2)) -> ret (ts1, ts2)
        | x -> fail (ExpectedUnqualidfiedCoderef x)
      in
      let* () = iterM ~f:push ts2 in
      let* it = instr_t_of env.kinds ts1 ts2 in
      ret @@ ICallIndirect it
  | Inject (None, i, ts) ->
      let* t_in = pop "Inject" in
      let* () = push (Sum ts) in
      let* it = instr_t_of env.kinds [ t_in ] [ Sum ts ] in
      ret @@ IInject (it, Z.of_int i)
  | Inject (Some mem, i, ts) ->
      let* t_in = pop "Inject" in
      let t_out = A.Type.(Ref (Base mem, Variant ts)) in
      let* () = push t_out in
      let* it = instr_t_of env.kinds [ t_in ] [ t_out ] in
      ret @@ IInjectNew (it, Z.of_int i)
  | Case (bt, lfx, cases) ->
      let* consume, result, env', st_inner = handle_bt ~lfx bt in
      let* cases', st's =
        foldM cases ~init:[] ~f:(fun acc case ->
            let+ case', st' = elab_block env' case st_inner in
            (case', st') :: acc)
        >>| List.rev
        >>| List.unzip
      in
      let* locals =
        let* curr_locals = get >>| fun st -> st.locals in
        foldiM st's ~init:None ~f:(fun i acc st ->
            let+ () =
              match lfx with
              | LocalFx lfx -> verify_lfx st lfx (sprintf "case::%i" i)
              | InferFx ->
                  (match acc with
                  | None -> ret ()
                  | Some prev_locals ->
                      compare_lfx
                        (fun j a b -> CannotInferLfx (`Case (i, j, a, b)))
                        st.locals prev_locals)
            in
            Some st.locals)
        >>| Option.value ~default:curr_locals
      in
      let* lfx' = handle_new_locals env locals in
      let* it = instr_t_of env.kinds consume result in
      ret @@ ICase (it, lfx', cases')
  | CaseLoad (bt, consume, lfx, cases) -> fail (TODO "case_load")
  | Group i ->
      (* top ... bottom -> bottom ... top *)
      let* ts =
        List.init i ~f:(fun _ -> ())
        |> mapiM ~f:(fun i _ -> pop (sprintf "Group-%i" i))
        >>| List.rev
      in
      let* () = push (Prod ts) in
      let* it = instr_t_of env.kinds ts [ Prod ts ] in
      ret @@ IGroup it
  | Ungroup ->
      let* ts =
        pop "Ungroup" >>= function
        | Prod ts -> ret ts
        | x -> fail (UngroupNonProd x)
      in
      let* () = iterM ~f:push ts in
      let* it = instr_t_of env.kinds [ Prod ts ] ts in
      ret @@ IUngroup it
  | Fold t ->
      let* k, t_inner =
        match t with
        | Rec (k, inner) -> ret (k, inner)
        | x -> fail (FoldNonRec x)
      in
      let expected_in =
        let open ASubst in
        T.subst M.var R.var S.var (scons (T.Rec (k, t_inner)) T.var) t_inner
      in
      let* it =
        mono_in_out env.kinds "Fold" [ expected_in ] [ Rec (k, t_inner) ]
      in
      ret @@ IFold it
  | Unfold ->
      let* k, t_inner =
        pop "Unfold" >>= function
        | Rec (k, t) -> ret (k, t)
        | x -> fail (UnfoldNonRec x)
      in
      let out =
        let open ASubst in
        T.subst M.var R.var S.var (scons (T.Rec (k, t_inner)) T.var) t_inner
      in
      let* () = push out in
      let* it = instr_t_of env.kinds [ Rec (k, t_inner) ] [ out ] in
      ret @@ IUnfold it
  | Pack (witness, t) ->
      let* tau = pop "Pack" in
      let tau0 =
        let open ASubst in
        (match witness with
          | Mem mem -> T.subst (scons mem M.var) R.var S.var T.var
          | Rep rep -> T.subst M.var (scons rep R.var) S.var T.var
          | Size sz -> T.subst M.var R.var (scons sz S.var) T.var
          | Type typ -> T.subst M.var R.var S.var (scons typ T.var))
        @@ t
      in
      let* () = fail_ifn (A.Type.equal tau tau0) (PackMismatch (tau, tau0)) in
      let* quanitfier =
        let open A.Quantifier in
        match witness with
        | Mem _ -> ret Memory
        | Rep _ -> ret Representation
        | Size _ -> ret Size
        | Type t ->
            let* kind =
              let open Result in
              elab_type env.kinds t
              >>= kind_of_typ env.kinds
              >>| unelab_kind
              |> lift_result
            in
            ret (Type kind)
      in
      let out_t : A.Type.t = Exists (quanitfier, t) in
      let* () = push out_t in
      let* it = instr_t_of env.kinds [ tau ] [ out_t ] in
      ret @@ IPack it
  | Unpack (bt, lfx, instrs) ->
      let* t_pkg = pop "Unpack" in
      let* shift_fn, t_body, new_k =
        let open ASubst in
        let add1 i = i + 1 in
        match t_pkg with
        | Exists (Memory, t) -> ret (T.ren add1 id id id, t, None)
        | Exists (Representation, t) -> ret (T.ren id add1 id id, t, None)
        | Exists (Size, t) -> ret (T.ren id id add1 id, t, None)
        | Exists (Type k, t) -> ret (T.ren id id id add1, t, Some k)
        | x -> fail (UnpackExpectsExists x)
      in

      let* st = get in
      let shifted_stack = List.map ~f:shift_fn st.stack in
      let st_inner_init = { st with stack = t_body :: shifted_stack } in
      let* () = put st_inner_init in
      let* consume, result, env', st_inner = handle_bt ~lfx bt in
      let env'' =
        match new_k with
        | Some k -> { env' with kinds = k :: env'.kinds }
        | None -> env'
      in
      let* instrs', st' = elab_block env'' instrs st_inner in

      (* unshift stack *)
      let* () = modify (fun new_st -> { new_st with stack = st.stack }) in
      let* lfx' =
        match lfx with
        | LocalFx lfx ->
            let* () = verify_lfx st' lfx "unpack" in
            handle_local_fx env lfx
        | InferFx -> handle_new_locals env st'.locals
      in
      let* () = iterM result ~f:push in
      let* it = instr_t_of env.kinds [ t_pkg ] result in
      ret @@ IUnpack (it, lfx', instrs')
  | Tag ->
      let* it = mono_in_out env.kinds "Tag" [ Num (Int I32) ] [ I31 ] in
      ret @@ ITag it
  | Untag ->
      let* it = mono_in_out env.kinds "Untag" [ I31 ] [ Num (Int I32) ] in
      ret @@ IUntag it
  | Cast typ ->
      let* in_t = pop "Cast" in
      let* () = push typ in
      let* it = instr_t_of env.kinds [ in_t ] [ typ ] in
      ret @@ ICast it
  | New m ->
      let* in_t = pop "New" in
      let out_t : A.Type.t = Ref (Base m, Ser in_t) in
      let* () = push out_t in
      let* it = instr_t_of env.kinds [ in_t ] [ out_t ] in
      ret @@ INew it
  | Load (path, consume) ->
      let* in_t = pop "Load" in
      let* mem, t_targ =
        match in_t with
        | Ref (mem, t) -> ret (mem, t)
        | t -> fail (NonRef (`Load, t))
      in
      let* t_targ' = elab_type env.kinds t_targ |> lift_result in

      let* pr_copy = resolves_path t_targ path None |> lift_result in
      let* t_val =
        match pr_copy.target with
        | Ser t -> ret t
        | x -> fail @@ LoadRefNonSer x
      in
      let* t_val' = elab_type env.kinds t_val |> lift_result in
      let* ex_copyable =
        ret t_val' >>=^ copyability_of_typ env.kinds >>| function
        | ImCopy | ExCopy -> true
        | _ -> false
      in
      let* should_move = is_effective_move consume ex_copyable |> lift_result in
      let* out_ts, consume' =
        if should_move then
          let* replaced_size =
            ret t_targ' >>=^ size_of_typ env.kinds >>| unelab_size
          in
          let+ pr =
            resolves_path t_targ path (Some (Span replaced_size)) |> lift_result
          in

          (A.Type.[ Ref (mem, pr.replaced); t_val ], B.Consumption.Move)
        else
          ret ([ in_t; t_val ], B.Consumption.Copy)
      in
      let path' = elab_path path in
      let* it = instr_t_of env.kinds [ in_t ] out_ts in
      let* () = out_ts |> iterM ~f:push in
      ret @@ ILoad (it, path', consume')
  | Store path ->
      (* NOTE: always treat as HStoreStrong; type checker will reject if invalid *)
      let* t = pop "Store-1" in
      let* ref = pop "Store-2" in
      let* mem, inner_t =
        match ref with
        | Ref (mem, t) -> ret (mem, t)
        | t -> fail (NonRef (`Store, t))
      in
      let* pr = resolves_path inner_t path (Some (Ser t)) |> lift_result in
      let path' = elab_path path in
      let res : A.Type.t = Ref (mem, pr.replaced) in
      let* it = instr_t_of env.kinds [ ref; t ] [ res ] in
      let* () = push res in
      ret @@ IStore (it, path')
  | Swap path ->
      let* t = pop "Swap-1" in
      let* ref = pop "Swap-2" in
      let* () =
        match ref with
        | Ref _ -> ret ()
        | t -> fail (NonRef (`Swap, t))
      in
      let path' = elab_path path in
      let* it = instr_t_of env.kinds [ ref; t ] [ ref; t ] in
      let* () = push ref in
      let* () = push t in
      ret @@ IStore (it, path')

let elab_function (env : Env.t) ({ typ; locals; body } : A.Module.Function.t) :
    B.Module.Function.t t =
  let* mf_type = elab_function_type [] typ in
  let mf_locals = List.map ~f:elab_representation locals in
  let (FunctionType (qs, in_t, return)) = typ in
  let init_locals = in_t @ List.map ~f:(fun rep -> A.Type.Plug rep) locals in
  let init_state = State.make ~locals:init_locals () in
  let kinds =
    List.filter_map
      ~f:(function
        | A.Quantifier.Memory | Representation | Size -> None
        | Type k -> Some k)
      qs
    |> List.rev
  in
  let local_offset = List.length in_t in
  let init_env = { env with return; kinds; local_offset } in
  let* mf_body, _ =
    let open InstrM in
    mapM body
      ~f:(fun instr ->
        fun state ->
         let res = elab_instruction init_env instr state in
         match res with
         | Ok x -> Ok x
         | Error error ->
             Error (InstrErr { error; instr; env = init_env; state }))
      init_state
  in

  ret @@ B.Module.Function.{ mf_type; mf_locals; mf_body }

let elab_module_export ({ name; desc = Func desc } : A.Module.Export.t) :
    B.Module.Export.t =
  { me_name = name; me_desc = Z.of_int desc }

let elab_module ({ imports; functions; table; exports } : A.Module.t) :
    B.Module.t t =
  let* m_imports = mapM ~f:(elab_function_type []) imports in
  let* env =
    let functions_typs = List.map ~f:(fun { typ; _ } -> typ) functions in
    let+ table_typs =
      mapM
        ~f:(fun i ->
          List.nth functions_typs i |> lift_option (InvalidTableIdxModule i))
        table
    in
    Env.make ~functions:functions_typs ~table:table_typs ~local_offset:0
      ~lfx:None ()
  in
  let* m_functions = mapM ~f:(elab_function env) functions in
  let m_table = List.map ~f:Z.of_int table in
  let m_exports = List.map ~f:elab_module_export exports in
  ret @@ B.Module.{ m_imports; m_functions; m_table; m_exports }
