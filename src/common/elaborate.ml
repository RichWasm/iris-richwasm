open! Base
open! Monads
open Stdlib.Format
module A = Syntax
module B = Annotated_syntax

module Err = struct
  type t =
    | TODO
    | InvalidLocalFx of (int * (int * A.Type.t) list)
    | TVarNotInEnv of (int * B.Kind.t list)
    | PopEmptyStack of string
    | ExpectedEqStack of (string * A.Type.t * A.Type.t)
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = ResultM (Err)

module Env = struct
  type t = {
    kinds : A.Kind.t list;
    labels : A.Type.t list list;
    return : A.Type.t list;
  }
  [@@deriving make, sexp]
end

module State = struct
  type t = {
    (* TODO: use annotated types w/ kinds *)
    locals : A.Type.t option list;
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
end

open Res

let elab_copyability : A.Copyability.t -> B.Copyability.t = function
  | NoCopy -> NoCopy
  | ImCopy -> ImCopy
  | ExCopy -> ExCopy

let elab_dropability : A.Dropability.t -> B.Dropability.t = function
  | NoDrop -> NoDrop
  | ImDrop -> ImDrop
  | ExDrop -> ExDrop

let elab_concrete_memory : A.ConcreteMemory.t -> B.ConcreteMemory.t = function
  | MM -> MemMM
  | GC -> MemGC

let elab_memory : A.Memory.t -> B.Memory.t = function
  | Var x -> VarM (Z.of_int x)
  | Concrete m -> ConstM (elab_concrete_memory m)

let elab_primitive_rep : A.PrimitiveRep.t -> B.PrimitiveRep.t = function
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
  | Prim rep -> PrimR (elab_primitive_rep rep)

let rec elab_size : A.Size.t -> B.Size.t = function
  | Var x -> VarS (Z.of_int x)
  | Sum sizes -> SumS (List.map ~f:elab_size sizes)
  | Prod sizes -> ProdS (List.map ~f:elab_size sizes)
  | Rep rep -> RepS (elab_representation rep)
  | Const s -> ConstS (Z.of_int s)

let elab_sizity : A.Sizity.t -> B.Sizity.t = function
  | Sized size -> Sized (elab_size size)
  | Unsized -> Unsized

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
  | Ser t ->
      let* t' = elab_type env t in
      (* TODO: kind of t -> VALTYPE has rep and dropability *)
      let* rep = fail TODO in
      let* mem = fail TODO in
      let* dropability = fail TODO in
      let+ () = ret () in
      SerT (MEMTYPE (Sized (RepS rep), mem, dropability), t')
  | Rec t ->
      let* kind = fail TODO in
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

(* TODO: block type *)

let elab_local_fx
    (env : A.Kind.t list)
    (num_locals : int)
    (LocalFx fxs : A.LocalFx.t) : B.Type.t option list Res.t =
  let arr = Array.init num_locals ~f:(fun _ -> None) in
  let+ () =
    iterM fxs ~f:(fun (idx, typ) ->
        let* () =
          fail_if (idx >= num_locals) (InvalidLocalFx (num_locals, fxs))
        in
        let+ typ' = elab_type env typ in
        arr.(idx) <- Some typ')
  in
  List.of_array arr

let elab_index (env : A.Kind.t list) : A.Index.t -> B.Index.t t =
  let open B.Index in
  function
  | Mem mem -> ret @@ MemI (elab_memory mem)
  | Rep rep -> ret @@ RepI (elab_representation rep)
  | Size size -> ret @@ SizeI (elab_size size)
  | Type typ -> elab_type env typ >>= fun t -> ret (TypeI t)

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

let rec elab_instruction (env : Env.t) :
    A.Instruction.t -> B.Instruction.t InstrM.t =
  let open InstrM in
  let open B.Instruction in
  (* let combine_its (its : B.InstructionType.t list) = *)
  (*   List.fold its ~init:[] ~f:(fun acc it -> *)
  (*      *)
  (* ) *)
  (* in *)
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
      (* | Block (bt, lfx, instrs) -> *)
      (*   let env' = {env with labels = bt :: env.labels} in *)
      (*   let* st = get in *)
      (*   let* instrs', st' = lift_result @@ mapM ~f:(elab_instruction env') instrs st in *)
      (*   let* () = fail TODO (* check lfx *) in *)
      (*   let  *)
  | _ -> fail TODO

let elab_function ({ typ; locals; body } : A.Module.Function.t) :
    B.Module.Function.t t =
  let* mf_type = elab_function_type [] typ in
  let mf_locals = List.map ~f:elab_representation locals in
  let (FunctionType (_, _, return)) = typ in
  (* TODO: setup qual env *)
  let init_locals = List.map ~f:(fun _ -> None) locals in
  let init_state = State.make ~locals:init_locals () in
  let init_env = Env.make ~return () in
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
