open! Base
open! Monads
open Stdlib.Format
module A = Syntax
module B = Annotated_syntax

let scons (x : 'a) (xi : Z.t -> 'a) (n : Z.t) : 'a =
  if Z.equal Z.zero n then x else xi (Z.sub n Z.one)

module Err = struct
  type t =
    | TODO
    | InvalidLocalFx of (int * (int * A.Type.t) list)
    | TVarNotInEnv of (int * B.Kind.t list)
    | PopEmptyStack of string
    | ExpectedEqStack of (string * A.Type.t * A.Type.t)
    | InvalidLabel of int
    | UnexpectedUnitializedLocal of int
    | InvalidLocalIdx of int
    | CannotCopyNonCopyable
    | InvalidTableIdx of int
    | InstNonCoderef of A.Type.t
    | InvalidFunctionIdx of int
    | CallNotFullyInstanciated of B.FunctionType.t
    | ExpectedVALTYPE of B.Type.t
    | ExpectedUnqualidfiedCoderef of A.Type.t
    | UngroupNonProd of A.Type.t
    | UnfoldNonRec of A.Type.t
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
end

module State = struct
  type t = {
    (* TODO: use annotated types w/ kinds *)
    locals : (A.Type.t * bool) option list;
    (* TODO: switch to B.Type.t and remove unlab_* *)
    stack : A.Type.t list;
  }
  [@@deriving make, sexp]
end

module InstrM = struct
  include StateM (State) (Err)

  let push (t : A.Type.t) : unit t =
    modify (fun s -> { s with stack = t :: s.stack })

  let pop (ctx : string) : A.Type.t t =
    let* st = get in
    match st.stack with
    | [] -> fail (PopEmptyStack ctx)
    | top :: rst ->
        let+ () = put { st with stack = rst } in
        top

  let set_local (i : int) (t : A.Type.t) (c : bool) : unit t =
    let* st = get in
    let* () = fail_if (List.length st.locals <= i) (InvalidLocalIdx i) in
    let locals' =
      List.mapi st.locals ~f:(fun i' x -> if i <> i' then x else Some (t, c))
    in
    modify (fun st -> { st with locals = locals' })

  let reset_local (i : int) : unit t =
    let* st = get in
    let* () = fail_if (List.length st.locals <= i) (InvalidLocalIdx i) in
    let locals' =
      List.mapi st.locals ~f:(fun i' x -> if i <> i' then x else None)
    in
    modify (fun st -> { st with locals = locals' })
end

open Res

let unelab_copyability : B.Copyability.t -> A.Copyability.t = function
  | NoCopy -> NoCopy
  | ImCopy -> ImCopy
  | ExCopy -> ExCopy

let elab_copyability : A.Copyability.t -> B.Copyability.t = function
  | NoCopy -> NoCopy
  | ImCopy -> ImCopy
  | ExCopy -> ExCopy

let unelab_dropability : B.Dropability.t -> A.Dropability.t = function
  | NoDrop -> NoDrop
  | ImDrop -> ImDrop
  | ExDrop -> ExDrop

let elab_dropability : A.Dropability.t -> B.Dropability.t = function
  | NoDrop -> NoDrop
  | ImDrop -> ImDrop
  | ExDrop -> ExDrop

let unelab_concrete_memory : B.ConcreteMemory.t -> A.ConcreteMemory.t = function
  | MemMM -> MM
  | MemGC -> GC

let elab_concrete_memory : A.ConcreteMemory.t -> B.ConcreteMemory.t = function
  | MM -> MemMM
  | GC -> MemGC

let unelab_memory : B.Memory.t -> A.Memory.t = function
  | VarM x -> Var (Z.to_int x)
  | ConstM m -> Concrete (unelab_concrete_memory m)

let elab_memory : A.Memory.t -> B.Memory.t = function
  | Var x -> VarM (Z.of_int x)
  | Concrete m -> ConstM (elab_concrete_memory m)

let unelab_primimive_rep : B.PrimitiveRep.t -> A.PrimitiveRep.t = function
  | PtrR -> Ptr
  | I32R -> I32
  | I64R -> I64
  | F32R -> F32
  | F64R -> F64

let elab_primitive_rep : A.PrimitiveRep.t -> B.PrimitiveRep.t = function
  | Ptr -> PtrR
  | I32 -> I32R
  | I64 -> I64R
  | F32 -> F32R
  | F64 -> F64R

let rec unelab_representation : B.Representation.t -> A.Representation.t =
  function
  | VarR x -> Var (Z.to_int x)
  | SumR reps -> Sum (List.map ~f:unelab_representation reps)
  | ProdR reps -> Prod (List.map ~f:unelab_representation reps)
  | PrimR rep -> Prim (unelab_primimive_rep rep)

let rec elab_representation : A.Representation.t -> B.Representation.t =
  function
  | Var x -> VarR (Z.of_int x)
  | Sum reps -> SumR (List.map ~f:elab_representation reps)
  | Prod reps -> ProdR (List.map ~f:elab_representation reps)
  | Prim rep -> PrimR (elab_primitive_rep rep)

let rec unelab_size : B.Size.t -> A.Size.t = function
  | VarS x -> Var (Z.to_int x)
  | SumS sizes -> Sum (List.map ~f:unelab_size sizes)
  | ProdS sizes -> Prod (List.map ~f:unelab_size sizes)
  | RepS rep -> Rep (unelab_representation rep)
  | ConstS s -> Const (Z.to_int s)

let rec elab_size : A.Size.t -> B.Size.t = function
  | Var x -> VarS (Z.of_int x)
  | Sum sizes -> SumS (List.map ~f:elab_size sizes)
  | Prod sizes -> ProdS (List.map ~f:elab_size sizes)
  | Rep rep -> RepS (elab_representation rep)
  | Const s -> ConstS (Z.of_int s)

let unelab_sizity : B.Sizity.t -> A.Sizity.t = function
  | Sized size -> Sized (unelab_size size)
  | Unsized -> Unsized

let elab_sizity : A.Sizity.t -> B.Sizity.t = function
  | Sized size -> Sized (elab_size size)
  | Unsized -> Unsized

let unelab_kind : B.Kind.t -> A.Kind.t = function
  | VALTYPE (representation, copyability, dropability) ->
      VALTYPE
        ( unelab_representation representation,
          unelab_copyability copyability,
          unelab_dropability dropability )
  | MEMTYPE (sizity, memory, dropability) ->
      MEMTYPE
        ( unelab_sizity sizity,
          unelab_memory memory,
          unelab_dropability dropability )

let elab_kind : A.Kind.t -> B.Kind.t = function
  | VALTYPE (representation, copyability, dropability) ->
      VALTYPE
        ( elab_representation representation,
          elab_copyability copyability,
          elab_dropability dropability )
  | MEMTYPE (sizity, memory, dropability) ->
      MEMTYPE
        (elab_sizity sizity, elab_memory memory, elab_dropability dropability)

let elab_sign : A.Sign.t -> B.Sign.t = function
  | Unsigned -> SignU
  | Signed -> SignS

let unelab_int_type : B.Int.Type.t -> A.Int.Type.t = function
  | I32T -> I32
  | I64T -> I64

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

let unelab_float_type : B.Float.Type.t -> A.Float.Type.t = function
  | F64T -> F64
  | F32T -> F32

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

let unelab_num_type : B.NumType.t -> A.NumType.t = function
  | IntT int_type -> Int (unelab_int_type int_type)
  | FloatT float_type -> Float (unelab_float_type float_type)

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

(* let meet_kind : B.Kind.t -> B.Kind.t -> B.Kind.t =
  function 
  | VALKIND *)
let kind_of_typ (env : B.Kind.t list) : B.Type.t -> B.Kind.t t = function
  | VarT x -> (
      let i = Z.to_int x in
      match List.nth env i with
      | Some x -> ret x
      | None -> fail (TVarNotInEnv (i, env)))
  | I31T k -> ret k
  | NumT (k, _)
  | SumT (k, _)
  | VariantT (k, _)
  | ProdT (k, _)
  | StructT (k, _)
  | RefT (k, _, _)
  | GCPtrT (k, _)
  | CodeRefT (k, _)
  | PadT (k, _, _)
  | SerT (k, _)
  | RecT (k, _)
  | ExistsMemT (k, _)
  | ExistsRepT (k, _)
  | ExistsSizeT (k, _)
  | ExistsTypeT (k, _, _) -> ret k

let rec unelab_type : B.Type.t -> A.Type.t = function
  | VarT x -> Var (Z.to_int x)
  | I31T _ -> I31
  | NumT (_, nt) -> Num (unelab_num_type nt)
  | SumT (_, ts) -> Sum (List.map ~f:unelab_type ts)
  | VariantT (_, ts) -> Variant (List.map ~f:unelab_type ts)
  | ProdT (_, ts) -> Prod (List.map ~f:unelab_type ts)
  | StructT (_, ts) -> Struct (List.map ~f:unelab_type ts)
  | RefT (_, mem, t) -> Ref (unelab_memory mem, unelab_type t)
  | GCPtrT (_, t) -> GCPtr (unelab_type t)
  | CodeRefT (_, ft) -> CodeRef (unelab_function_type ft)
  | PadT (_, size, t) -> Pad (unelab_size size, unelab_type t)
  | SerT (MEMTYPE (_, mem, _), t) -> Ser (unelab_memory mem, unelab_type t)
  | SerT (_, _) -> failwith "invalid ser"
  | RecT (kind, t) -> Rec (unelab_kind kind, unelab_type t)
  | ExistsMemT (_, t) -> Exists (Memory, unelab_type t)
  | ExistsRepT (_, t) -> Exists (Representation, unelab_type t)
  | ExistsSizeT (_, t) -> Exists (Size, unelab_type t)
  | ExistsTypeT (_, k, t) -> Exists (Type (unelab_kind k), unelab_type t)

and unelab_function_type (ft : B.FunctionType.t) : A.FunctionType.t =
  let rec go (qs : A.Quantifier.t list) : B.FunctionType.t -> A.FunctionType.t =
    function
    | MonoFunT (ts1, ts2) ->
        let ts1' = List.map ~f:unelab_type ts1 in
        let ts2' = List.map ~f:unelab_type ts2 in
        FunctionType (qs, ts1', ts2')
    | ForallMemT ft -> go (Memory :: qs) ft
    | ForallRepT ft -> go (Representation :: qs) ft
    | ForallSizeT ft -> go (Size :: qs) ft
    | ForallTypeT (k, ft) -> go (Type (unelab_kind k) :: qs) ft
  in
  go [] ft

(* TODO: this needs to be double checked *)
let rec elab_type (env : A.Kind.t list) : A.Type.t -> B.Type.t t =
  let rep_of_nt : A.NumType.t -> B.PrimitiveRep.t = function
    | Int I32 -> I32R
    | Int I64 -> I64R
    | Float F32 -> F32R
    | Float F64 -> F64R
  in

  let meet_typs (typs : B.Type.t list) : B.Kind.t = failwith "TODO" in

  let open B.Type in
  function
  | Var x -> ret @@ VarT (Z.of_int x)
  | I31 -> ret @@ I31T (VALTYPE (PrimR PtrR, ImCopy, ImDrop))
  | Num nt ->
      let+ () = ret () in
      NumT (VALTYPE (PrimR (rep_of_nt nt), ImCopy, ImDrop), elab_num_type nt)
  | Sum ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let k = meet_typs ts' in
      ret @@ SumT (k, ts')
  | Variant ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* size = fail TODO in
      let* mem = fail TODO in
      let* dropability = fail TODO in
      let+ () = ret () in
      VariantT (MEMTYPE (size, mem, dropability), ts')
  | Prod ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let k = meet_typs ts' in
      ret @@ ProdT (k, ts')
  (* Struct [Num I32 ] *)
  | Struct ts ->
      let* ts' = mapM ~f:(elab_type env) ts in
      let* size = fail TODO in
      let* mem = fail TODO in
      let* dropability = fail TODO in
      let+ () = ret () in
      StructT (MEMTYPE (size, mem, dropability), ts')
  | Ref (Concrete MM, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (PrimR PtrR, NoCopy, ExDrop), ConstM MemMM, t')
  | Ref (Concrete GC, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (PrimR PtrR, ExCopy, ExDrop), ConstM MemGC, t')
  | Ref (mem, t) ->
      let+ t' = elab_type env t in
      RefT (VALTYPE (PrimR PtrR, NoCopy, NoDrop), elab_memory mem, t')
  | GCPtr t ->
      let+ t' = elab_type env t in
      GCPtrT (MEMTYPE (Sized (ConstS (Z.of_int 1)), ConstM MemGC, ImDrop), t')
  | CodeRef ft ->
      let+ ft' = elab_function_type env ft in
      CodeRefT (VALTYPE (PrimR I32R, ImCopy, ImDrop), ft')
  | Pad (size, t) ->
      let size' = elab_size size in
      let* t' = elab_type env t in
      let* mem = fail TODO in
      let* dropability = fail TODO in
      let+ () = ret () in
      PadT (MEMTYPE (Sized size', mem, dropability), size', t')
  | Ser (mem, t) ->
      let* t' = elab_type env t in
      let mem' = elab_memory mem in
      let* rep, dropability =
        kind_of_typ [] t' >>= function
        | VALTYPE (rep, _, dropability) -> ret (rep, dropability)
        | _ -> fail (ExpectedVALTYPE t')
      in
      ret @@ SerT (MEMTYPE (Sized (RepS rep), mem', dropability), t')
  | Rec (kind, t) ->
      let env' = kind :: env in
      let* t' = elab_type env' t in
      let kind' = elab_kind kind in
      let+ () = ret () in
      RecT (kind', t')
  (* TODO: do we need to keep track of all var? *)
  | Exists (Memory, t) ->
      let* t' = elab_type env t in
      let* kind = fail TODO in
      let+ () = ret () in
      ExistsMemT (kind, t')
  | Exists (Representation, t) ->
      let* t' = elab_type env t in
      let* kind = fail TODO in
      let+ () = ret () in
      ExistsMemT (kind, t')
  | Exists (Size, t) ->
      let* t' = elab_type env t in
      let* kind = fail TODO in
      let+ () = ret () in
      ExistsSizeT (kind, t')
  | Exists (Type k, t) ->
      let env' = k :: env in
      let* t' = elab_type env' t in
      let k' = elab_kind k in
      let* kind = fail TODO in
      let+ () = ret () in
      ExistsTypeT (kind, k', t')

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
    B.Type.t option list Res.t =
  let arr = Array.init env.local_offset ~f:(fun _ -> None) in
  let+ () =
    iterM fxs ~f:(fun (idx, typ) ->
        let* () =
          fail_if (idx >= env.local_offset)
            (InvalidLocalFx (env.local_offset, fxs))
        in
        let+ typ' = elab_type env.kinds typ in
        arr.(idx - env.local_offset) <- Some typ')
  in
  List.of_array arr

let elab_index (env : A.Kind.t list) : A.Index.t -> B.Index.t t =
  let open B.Index in
  function
  | Mem mem -> ret @@ MemI (elab_memory mem)
  | Rep rep -> ret @@ RepI (elab_representation rep)
  | Size size -> ret @@ SizeI (elab_size size)
  | Type typ -> elab_type env typ >>| fun t -> TypeI t

let elab_path (Path components : A.Path.t) : B.Path.t =
  let elab_component : A.Path.Component.t -> B.Path.Component.t = function
    | Proj i -> PCProj (Z.of_int i)
    | Unwrap -> PCSkip
  in
  List.map ~f:elab_component components

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
  let open B.InstructionType in
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
      let* it = instr_t_of kenv [ t_in1; t_in2 ] [ t_in1 ] in
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
      let* it = instr_t_of kenv [ t_in1; t_in2 ] [ t_out ] in
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
      let* it = instr_t_of kenv [ t_in1; t_in2 ] [ t_in1 ] in
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
      let* it = instr_t_of kenv [ t_in1; t_in2 ] [ t_out ] in
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

let function_typ_inst (idx : B.Index.t) (ft : B.FunctionType.t) =
  let open B.FunctionType in
  B.(
    match idx with
    | MemI mem ->
        subst (scons mem Memory.varM) Representation.varR Size.varS Type.varT
    | RepI rep ->
        subst Memory.varM (scons rep Representation.varR) Size.varS Type.varT
    | SizeI size ->
        subst Memory.varM Representation.varR (scons size Size.varS) Type.varT
    | TypeI typ ->
        subst Memory.varM Representation.varR Size.varS (scons typ Type.varT))
    ft

let function_typ_insts (idxs : B.Index.t list) (ft : B.FunctionType.t) =
  List.fold ~init:ft ~f:(fun ft idx -> function_typ_inst idx ft) idxs

let rec elab_instruction (env : Env.t) :
    A.Instruction.t -> B.Instruction.t InstrM.t =
  let open InstrM in
  let open B.Instruction in
  (* let combine_its (its : B.InstructionType.t list) = *)
  (*   List.fold its ~init:[] ~f:(fun acc it -> *)
  (*      *)
  (* ) *)
  (* in *)
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
      let* () =
        ignore st';
        fail TODO (* check lfx *)
      in
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
      let* () =
        ignore thn_st;
        ignore els_st;
        fail TODO
      in
      let* lfx' = lift_result @@ elab_local_fx env lfx in
      let* it = instr_t_of env.kinds consume result in
      ret @@ IIte (it, lfx', thn', els')
  | Br label ->
      let* st = get in
      let* result =
        match List.nth env.labels label with
        | Some t -> ret t
        | None -> fail (InvalidLabel label)
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
        match List.nth st.locals i with
        | Some (Some (t, c)) -> ret (t, c)
        | Some None -> fail (UnexpectedUnitializedLocal i)
        | None -> fail (InvalidLocalIdx i)
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
      let* copyable =
        let open Res in
        kind_of_typ (List.map ~f:elab_kind env.kinds) t'
        >>| ( function
        | VALTYPE (_, ImCopy, _) -> true
        | _ -> false )
        |> lift_result
      in
      let* () = set_local i t copyable in
      ret @@ ILocalSet (InstrT ([], [ t' ]), Z.of_int i)
  | CodeRef i ->
      let* ft =
        match List.nth env.table i with
        | Some ft -> ret ft
        | None -> fail (InvalidTableIdx i)
      in
      let* it = mono_in_out env.kinds "CodeRef" [] [ CodeRef ft ] in
      ret @@ ICodeRef (it, Z.of_int i)
  | Inst idx ->
      let* ft =
        pop "Inst" >>= function
        | CodeRef ft -> ret ft
        | x -> fail (InstNonCoderef x)
      in

      let* ft' = elab_function_type env.kinds ft |> lift_result in
      let* idx' = elab_index env.kinds idx |> lift_result in
      let ft'' = function_typ_inst idx' ft' in
      (* FIXME: repeated *)
      let k : B.Kind.t = VALTYPE (PrimR I32R, ImCopy, ImDrop) in
      let it : B.InstructionType.t =
        InstrT ([ CodeRefT (k, ft') ], [ CodeRefT (k, ft'') ])
      in
      let* () = push (unelab_type (CodeRefT (k, ft''))) in
      ret @@ IInst (it, idx')
  | Call (i, idxs) ->
      let* idxs' = Res.mapM ~f:(elab_index env.kinds) idxs |> lift_result in
      let* ft =
        match List.nth env.functions i with
        | Some x -> ret x
        | None -> fail (InvalidFunctionIdx i)
      in
      let* ft' = elab_function_type env.kinds ft |> lift_result in
      let* ts1, ts2 =
        match function_typ_insts idxs' ft' with
        | MonoFunT (ts1, ts2) -> ret (ts1, ts2)
        | x -> fail (CallNotFullyInstanciated x)
      in
      let ts1_a, ts2_a =
        (List.map ~f:unelab_type ts1, List.map ~f:unelab_type ts2)
      in
      let* it = mono_in_out env.kinds "Call" ts1_a ts2_a in
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
      let t_out = A.Type.(Ref (Concrete mem, Variant ts)) in
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
            ignore case';
            ignore st';
            ignore acc;
            fail TODO)
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
      let* it = instr_t_of env.kinds ts [Prod ts] in
      ret @@ IGroup it
  | Ungroup ->
      let* ts = pop "Ungroup" >>= (function 
        | Prod ts -> ret ts
        | x -> fail (UngroupNonProd x)) in
      let* () = iterM ~f:push ts in
      let* it = instr_t_of env.kinds [Prod ts] ts in
      ret @@ IUngroup it
  | Fold t ->
      let* t = pop "Fold" in
      fail TODO
  | Unfold ->
      let* (k, inner_t) = pop "Unfold" >>= function 
        | Rec (k, t) -> ret (k, t)
        | x -> fail (UnfoldNonRec x) in
      fail TODO
  | _ -> fail TODO

let elab_function ({ typ; locals; body } : A.Module.Function.t) :
    B.Module.Function.t t =
  let* mf_type = elab_function_type [] typ in
  let mf_locals = List.map ~f:elab_representation locals in
  let (FunctionType (_, _, return)) = typ in
  (* TODO: setup qual env *)
  let init_locals = List.map ~f:(fun _ -> None) locals in
  let init_state = State.make ~locals:init_locals () in
  let init_env = Env.make ~return ~local_offset:1 () in
  let* mf_body, _ =
    InstrM.mapM body ~f:(elab_instruction init_env) init_state
  in
  ret @@ B.Module.Function.{ mf_type; mf_locals; mf_body }

let elab_module ({ imports; functions; table; exports } : A.Module.t) :
    B.Module.t t =
  let* m_imports = mapM ~f:(elab_function_type []) imports in
  let* m_functions = mapM ~f:elab_function functions in
  let m_table = List.map ~f:Z.of_int table in
  let m_exports = List.map ~f:Z.of_int exports in
  ret @@ B.Module.{ m_imports; m_functions; m_table; m_exports }
