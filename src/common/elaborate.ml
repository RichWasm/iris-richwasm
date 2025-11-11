open! Base
open! Monads
open Stdlib.Format
module A = Syntax
module B = Annotated_syntax

module Err = struct
  type t =
    | TODO of string
    | InvalidLocalFx of (int * (int * A.Type.t) list)
    | TVarNotInEnv of (int * A.Kind.t list)
    | PopEmptyStack of string
    | ExpectedEqStack of (string * A.Type.t * A.Type.t)
    | InvalidLabel of int
    | UnexpectedUnitializedLocal of int
    | InvalidLocalIdx of (int * [ `Set | `Get | `Reset ])
    | CannotCopyNonCopyable
    | InvalidTableIdx of int
    | InvalidTableIdxModule of int
    | InstNonCoderef of A.Type.t
    | InvalidFunctionIdx of int
    | CallNotFullyInstanciated of A.FunctionType.t
    | ExpectedVALTYPE of string * B.Type.t
    | ExpectedMEMTYPE of string * B.Type.t
    | CannotMeet of string * B.Kind.t
    | ExpectedUnqualidfiedCoderef of A.Type.t
    | UngroupNonProd of A.Type.t
    | FoldNonRec of A.Type.t
    | UnfoldNonRec of A.Type.t
    | FunctionParamMustBeMonoRep
    | ParamMustBeMemType of B.Kind.t
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = ResultM (Err)

module Env = struct
  type t = {
    local_offset : int;
    kinds : A.Kind.t list;
    labels : A.Type.t list list;
    return : A.Type.t list;
    functions : A.FunctionType.t list;
    table : A.FunctionType.t list;
  }
  [@@deriving make, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module State = struct
  type t = {
    locals : (A.Type.t * bool) option list;
    stack : A.Type.t list;
  }
  [@@deriving make, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

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

  let set_local (i : int) (t : Type.t) (c : bool) : unit t =
    let* st = get in
    let* () =
      fail_if (List.length st.locals <= i) (InvalidLocalIdx (i, `Set))
    in
    let locals' =
      List.mapi st.locals ~f:(fun i' x -> if i <> i' then x else Some (t, c))
    in
    modify (fun st -> { st with locals = locals' })

  let reset_local (i : int) : unit t =
    let* st = get in
    let* () =
      fail_if (List.length st.locals <= i) (InvalidLocalIdx (i, `Reset))
    in
    let locals' =
      List.mapi st.locals ~f:(fun i' x -> if i <> i' then x else None)
    in
    modify (fun st -> { st with locals = locals' })
end

open Res

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

let unelab_atomic_rep : B.AtomicRep.t -> A.AtomicRep.t = function
  | PtrR -> Ptr
  | I32R -> I32
  | I64R -> I64
  | F32R -> F32
  | F64R -> F64

let rec elab_representation : A.Representation.t -> B.Representation.t =
  function
  | Var x -> VarR (Z.of_int x)
  | Sum reps -> SumR (List.map ~f:elab_representation reps)
  | Prod reps -> ProdR (List.map ~f:elab_representation reps)
  | Atom rep -> AtomR (elab_atomic_rep rep)

let rec unelab_representation : B.Representation.t -> A.Representation.t =
  function
  | VarR x -> Var (Z.to_int x)
  | SumR reps -> Sum (List.map ~f:unelab_representation reps)
  | ProdR reps -> Prod (List.map ~f:unelab_representation reps)
  | AtomR rep -> Atom (unelab_atomic_rep rep)

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

  let open B.Type in
  function
  | Var x -> ret @@ VarT (Z.of_int x)
  | I31 -> ret @@ I31T (VALTYPE (AtomR PtrR, ImCopy, ImDrop))
  | Num nt ->
      let+ () = ret () in
      NumT (VALTYPE (AtomR (rep_of_nt nt), ImCopy, ImDrop), elab_num_type nt)
  | Sum ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = mapM ~f:(kind_of_typ env) ts' >>= meet_valtypes sumR in
      ret @@ SumT (k, ts')
  | Variant ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = mapM ~f:(kind_of_typ env) ts' >>= meet_memtypes sumS in
      ret @@ VariantT (k, ts')
  | Prod ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = mapM ~f:(kind_of_typ env) ts' >>= meet_valtypes prodR in
      ret @@ ProdT (k, ts')
  | Struct ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* k = mapM ~f:(kind_of_typ env) ts' >>= meet_memtypes prodS in
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
        | _ -> fail (ExpectedVALTYPE ("Ser", t'))
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

let elab_local_fx (env : Env.t) (LocalFx fxs : A.LocalFx.t) :
    B.Type.t list Res.t =
  fail (TODO "elab_local_fx")

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
  let* t_in' = lift_result @@ Res.mapM ~f:(elab_type env) t_in in
  let* t_out' = lift_result @@ Res.mapM ~f:(elab_type env) t_out in
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

let function_typ_inst (idx : A.Index.t) (ft : A.FunctionType.t) =
  let open A in
  let open FunctionType in
  let open Unscoped in
  (match idx with
  | Mem mem -> subst (scons mem Memory.var) Representation.var Size.var Type.var
  | Rep rep -> subst Memory.var (scons rep Representation.var) Size.var Type.var
  | Size size ->
      subst Memory.var Representation.var (scons size Size.var) Type.var
  | Type typ ->
      subst Memory.var Representation.var Size.var (scons typ Type.var))
    ft

let function_typ_insts (idxs : A.Index.t list) (ft : A.FunctionType.t) =
  List.fold ~init:ft ~f:(fun ft idx -> function_typ_inst idx ft) idxs

let is_local_copyable (kinds : A.Kind.t list) t =
  kind_of_typ kinds t >>| function
  | VALTYPE (_, ImCopy, _) -> true
  | _ -> false

let[@warning "-27"] rec elab_instruction (env : Env.t) :
    A.Instruction.t -> B.Instruction.t InstrM.t =
  let open InstrM in
  let open B.Instruction in
  let handle_bt (bt : A.BlockType.t) =
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
    let+ () = iterM result ~f:push in
    let env' = { env with labels = result :: env.labels } in
    let st_inner = { init_st with stack = consume } in
    (consume, result, env', st_inner)
  in
  function
  | Nop -> ret @@ INop (InstrT ([], []))
  | Unreachable ->
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
      let* consume, result, env', st_inner = handle_bt bt in
      let* instrs', st' =
        lift_result @@ mapM ~f:(elab_instruction env') instrs st_inner
      in
      let* () = fail (TODO "check lfx") in
      let* lfx' = lift_result @@ elab_local_fx env lfx in
      let* it = instr_t_of env.kinds consume result in
      ret @@ IBlock (it, lfx', instrs')
  | Loop (bt, instrs) ->
      let* consume, result, env', st_inner = handle_bt bt in
      let* instrs', _ =
        lift_result @@ mapM ~f:(elab_instruction env') instrs st_inner
      in
      let* it = instr_t_of env.kinds consume result in
      ret @@ ILoop (it, instrs')
  | Ite (bt, lfx, thn, els) ->
      let* consume, result, env', st_inner = handle_bt bt in
      let* thn', thn_st =
        lift_result @@ mapM ~f:(elab_instruction env') thn st_inner
      in
      let* els', els_st =
        lift_result @@ mapM ~f:(elab_instruction env') els st_inner
      in
      let* () = fail (TODO "check lfx") in
      let* lfx' = lift_result @@ elab_local_fx env lfx in
      let* it = instr_t_of env.kinds consume result in
      ret @@ IIte (it, lfx', thn', els')
  | Br label ->
      let* st = get in
      let* result =
        List.nth env.labels label |> lift_option (InvalidLabel label)
      in
      let* it = mono_in_out env.kinds "Br" st.stack result in
      ret @@ IBr (it, Z.of_int label)
  | Return ->
      let* st = get in
      let* it = mono_in_out env.kinds "Return" st.stack env.return in
      ret @@ IReturn it
  | LocalGet (i, consume) ->
      let* st = get in
      let* t, copyable =
        List.nth st.locals i
        |> lift_option (InvalidLocalIdx (i, `Get))
        >>= lift_option (UnexpectedUnitializedLocal i)
      in
      let* is_effective_consume =
        A.Consume.(
          match consume with
          | Follow -> ret @@ not copyable
          | Copy ->
              if not copyable then fail CannotCopyNonCopyable else ret false
          | Move -> ret true)
      in
      let* () =
        if is_effective_consume then
          reset_local i
        else
          ret ()
      in
      let* it = mono_in_out env.kinds "LocalGet" [] [ t ] in
      ret @@ ILocalGet (it, Z.of_int i)
  | LocalSet i ->
      let* t = pop "LocalSet" in
      let* t' = lift_result @@ elab_type env.kinds t in
      let* copyable = is_local_copyable env.kinds t' |> lift_result in
      let* () = set_local i t copyable in
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
      ret @@ IInject (it, Z.of_int i)
  | Case (bt, lfx, cases) ->
      let* consume, result, env', st_inner = handle_bt bt in
      let* lfx' = elab_local_fx env lfx |> lift_result in
      let* cases' =
        foldM cases ~init:[] ~f:(fun acc case ->
            let* case', st' =
              mapM ~f:(elab_instruction env') case st_inner |> lift_result
            in
            fail (TODO "case: check lfx, st management"))
      in
      let* it = instr_t_of env.kinds consume result in
      ret @@ ICase (it, lfx', cases')
  | Group i ->
      (* top .... bottom -> bottom .... top *)
      let* ts =
        List.init i ~f:(fun _ -> ())
        |> mapM ~f:(fun _ -> pop "Group")
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
        let open A in
        Type.subst Memory.var Representation.var Size.var
          Type.(Unscoped.scons (Rec (k, t_inner)) var)
          t_inner
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
        let open A in
        Type.subst Memory.var Representation.var Size.var
          Type.(Unscoped.scons (Rec (k, t_inner)) var)
          t_inner
      in
      let* () = push out in
      let* it = instr_t_of env.kinds [ Rec (k, t_inner) ] [ out ] in
      ret @@ IUnfold it
  | Pack (Mem mem, t) -> fail (TODO "pack")
  | Pack (Rep rep, t) -> fail (TODO "pack")
  | Pack (Size sz, t) -> fail (TODO "pack")
  | Pack (Type typ, t) -> fail (TODO "pack")
  | Unpack (bt, lfx, instrs) -> fail (TODO "unpack")
  | Tag ->
      let* it = mono_in_out env.kinds "Tag" [ Num (Int I32) ] [ I31 ] in
      ret @@ ITag it
  | Untag ->
      let* it = mono_in_out env.kinds "Untag" [ I31 ] [ Num (Int I32) ] in
      ret @@ IUntag it
  | Cast _ -> fail (TODO "cast")
  | New _ | Load (_, _) | Store _ | Swap _ -> fail (TODO "memory")

let function_param_reps (FunctionType (qs, in_t, _) : A.FunctionType.t) :
    (A.Type.t * bool) option list t =
  let kinds =
    List.filter_map
      ~f:(function
        | A.Quantifier.Memory | Representation | Size -> None
        | Type k -> Some k)
      qs
    |> List.rev
  in

  mapM ~f:(elab_type kinds) in_t
  >>= mapM ~f:(is_local_copyable kinds)
  >>| List.zip_exn in_t
  >>| List.map ~f:Option.return

let elab_function (env : Env.t) ({ typ; locals; body } : A.Module.Function.t) :
    B.Module.Function.t t =
  let* mf_type = elab_function_type [] typ in
  let mf_locals = List.map ~f:elab_representation locals in
  let (FunctionType (_, _, return)) = typ in
  let* param_locals = function_param_reps typ in
  let init_locals = param_locals @ List.map ~f:(fun _ -> None) locals in
  let init_state = State.make ~locals:init_locals () in
  (* TODO: setup qual env *)

  let init_env = { env with return; local_offset = List.length param_locals } in
  let* mf_body, _ =
    InstrM.mapM body ~f:(elab_instruction init_env) init_state
  in
  ret @@ B.Module.Function.{ mf_type; mf_locals; mf_body }

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
    Env.make ~functions:functions_typs ~table:table_typs ~local_offset:0 ()
  in
  let* m_functions = mapM ~f:(elab_function env) functions in
  let m_table = List.map ~f:Z.of_int table in
  let m_exports = List.map ~f:Z.of_int exports in
  ret @@ B.Module.{ m_imports; m_functions; m_table; m_exports }
