open! Base
open Syntax
open Richwasm_common.Syntax
open Richwasm_common.Monads

module Err = struct
  type t =
    | UnboundVar of string
    | ApplyNonClosure of Closed.PreType.t
    | ProjectNonProd of Closed.PreType.t
    | ProjectUnboxed of Closed.PreType.t
    | SplitNonUnboxed of Closed.PreType.t
    | SplitMismatch of Closed.Type.t list * Closed.PreType.t list
    | DerefNonRef of Closed.PreType.t
    | LinNonRef of Closed.PreType.t
    | UnfoldNonRec of Closed.PreType.t
    | EmptyCases
    | ApplyForallsLengthMismatch of int * int
    | TypeVarNotInDelta of string
    | InjNonSum of Closed.PreType.t
    | PackNonExists of Type.t
    | FoldNonRec of Type.t
    | VarNotInGamma of string
    | CoderefNotFound of string
    | ImportNotFunction of Type.t
  [@@deriving sexp_of, variants]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = ResultM (Err)

let rep : Representation.t = Atom Ptr

(** the kind of mini-ml type binders: [VALTYPE ptr gcrefs]. Every type is
    uniformly represented except unboxed tuples, which therefore cannot
    instantiate type variables; [lin] refs are uncopyable (anyrefs), so they
    cannot either. *)
let kind : Kind.t = VALTYPE (rep, GCRefs)

let rec rep_of_type : Type.t -> Representation.t = function
  | Prod ts -> Prod (List.map ~f:rep_of_type ts)
  | _ -> rep

(** whether the value itself is uncopyable, mirroring richwasm's kind flags:
    [lin] is an mm ref (anyrefs) and unboxed tuples lub their components, while
    boxed values are gc refs (gcrefs) no matter what their pointees hold. *)
let rec contains_lin : Closed.PreType.t -> bool = function
  | Lin _ -> true
  | UProd ts -> List.exists ~f:contains_lin ts
  | Int | Var _ | Code _ | Prod _ | Sum _ | Ref _ | Rec _ | Exists _ -> false

let rec type_subst var replacement tau =
  let open Closed.PreType in
  match tau with
  | Int -> Int
  | Prod ts -> Prod (List.map ~f:(type_subst var replacement) ts)
  | UProd ts -> UProd (List.map ~f:(type_subst var replacement) ts)
  | Sum ts -> Sum (List.map ~f:(type_subst var replacement) ts)
  | Ref t -> Ref (type_subst var replacement t)
  | Lin t -> Lin (type_subst var replacement t)
  | Rec (v, _) when equal_string v var -> tau
  | Rec (v, t) -> Rec (v, type_subst var replacement t)
  | Exists (v, _) when equal_string v var -> tau
  | Exists (v, t) -> Exists (v, type_subst var replacement t)
  | Var v when equal_string v var -> replacement
  | Var _ -> tau
  | Code { foralls; _ } when List.mem ~equal:equal_string foralls var -> tau
  | Code { foralls; arg; ret } ->
      Code
        {
          foralls;
          arg = type_subst var replacement arg;
          ret = type_subst var replacement ret;
        }

let rec type_of_e gamma (e : Closed.Expr.t) : Closed.PreType.t Res.t =
  let open Closed.PreType in
  let open Res in
  match e with
  | Inj (_, _, t) | Pack (_, _, t) | Coderef (t, _) -> ret t
  | Int _ -> ret Int
  | Tuple vs ->
      let* ts = mapM vs ~f:(type_of_e gamma) in
      ret (Prod ts)
  | UTuple vs ->
      let* ts = mapM vs ~f:(type_of_e gamma) in
      ret (UProd ts)
  | Var v ->
      (match List.Assoc.find ~equal:equal_string gamma v with
      | Some t -> ret t
      | None -> fail (Err.UnboundVar v))
  | Apply (f, ts, _) ->
      let* ft = type_of_e gamma f in
      (match ft with
      | Exists (_, Prod [ _; Code { foralls; ret = ret_t; _ } ]) ->
          (match List.fold_right2 foralls ts ~init:ret_t ~f:type_subst with
          | Ok t -> ret t
          | Unequal_lengths ->
              fail
                (ApplyForallsLengthMismatch (List.length foralls, List.length ts)))
      | _ -> fail (ApplyNonClosure ft))
  | Project (i, v) ->
      let* vt = type_of_e gamma v in
      (match vt with
      | Prod ts -> ret (List.nth_exn ts i)
      | UProd _ -> fail (ProjectUnboxed vt)
      | _ -> fail (ProjectNonProd vt))
  | Op _ -> ret Int
  | If0 (_, e, _) -> type_of_e gamma e
  | Cases (_, ((n, t), e) :: _) -> type_of_e ((n, t) :: gamma) e
  | Cases _ -> fail EmptyCases
  | New v ->
      let* t = type_of_e gamma v in
      ret (Ref t)
  | Deref v ->
      let* vt = type_of_e gamma v in
      (match vt with
      | Ref t -> ret t
      (* reading a lin ref must give the (unboxed) ref back alongside the value *)
      | Lin (Ref t) -> ret (UProd [ vt; t ])
      | _ -> fail (DerefNonRef vt))
  | Assign (re, _) ->
      let* rt = type_of_e gamma re in
      (* writing a lin ref must give the ref back; gc assigns return unit *)
      (match rt with
      | Lin _ -> ret rt
      | _ -> ret (Prod []))
  | Let ((n, t), _, e) -> type_of_e ((n, t) :: gamma) e
  | Split (bs, _, e) -> type_of_e (bs @ gamma) e
  | Fold (t, _) -> ret t
  | Unfold v ->
      let* vt = type_of_e gamma v in
      (match vt with
      | Rec (var, t) as tau -> ret (type_subst var tau t)
      | _ -> fail (Err.UnfoldNonRec vt))
  | Unpack (_, (n, t), _, e) -> type_of_e ((n, t) :: gamma) e

let rec compile_type delta (t : Closed.PreType.t) : Type.t Res.t =
  let open Type in
  let open Res in
  let r = compile_type delta in
  let r_ser t =
    let+ t' = r t in
    Ser t'
  in
  match t with
  | Int -> ret I31
  | Prod ts ->
      let+ ts' = mapM ~f:r_ser ts in
      Ref (Base GC, Imm, Struct ts')
  | UProd ts ->
      let+ ts' = mapM ~f:r ts in
      Prod ts'
  | Sum ts ->
      let+ ts' = mapM ~f:r_ser ts in
      Ref (Base GC, Imm, Variant ts')
  | Ref t ->
      let+ t' = r t in
      Ref (Base GC, Mut, Ser t')
  | Lin (Ref inner) ->
      (* NOTE: deref dispatches on the payload flag: gcrefs payloads copy out;
         lin payloads move out, leaving a span hole the next assign refills *)
      let+ inner' = r inner in
      Ref (Base MM, Mut, Ser inner')
  | Lin t -> fail (LinNonRef t)
  | Rec (v, t) ->
      let+ t' = compile_type (v :: delta) t in
      Rec (kind, t')
  | Exists (v, t) ->
      let+ t' = compile_type (v :: delta) t in
      Exists (Type kind, t')
  | Code { foralls; arg; ret = ret_t } ->
      let r = compile_type (foralls @ delta) in
      let* arg' = r arg in
      let+ ret' = r ret_t in
      CodeRef
        (FunctionType
           ( List.map ~f:(Fn.const (Quantifier.Type kind)) foralls,
             [ arg' ],
             [ ret' ] ))
  | Var v ->
      (match
         List.find_mapi delta ~f:(fun i name ->
             Option.some_if (equal_string name v) i)
       with
      | Some i -> ret (var i)
      | None -> fail (TypeVarNotInDelta v))

let rec compile_expr delta gamma locals coderef_map e :
    (Instruction.t list * (string * Type.t) list * (int * Type.t) list) Res.t =
  let open Res in
  let open Instruction in
  let unindexed = List.map ~f:(fun (n, t, _) -> (n, t)) gamma in
  let r = compile_expr delta gamma locals coderef_map in
  let r_list locals vs =
    foldM
      ~f:(fun (instrs, locals, fx) item ->
        let* v', locals', fx' =
          compile_expr delta gamma locals coderef_map item
        in
        ret (instrs @ v', locals', fx @ fx'))
      ~init:([], locals, []) vs
  in
  let* t = type_of_e unindexed e in
  let* rw_t = compile_type delta t in
  match e with
  | Int i ->
      let open NumType in
      ret ([ NumConst (Int I32, i); Tag ], locals, [])
  | Tuple vs ->
      let* vs', locals', fx = r_list locals vs in
      ret
        (vs' @ [ Group (List.length vs); New (GC, Imm); Cast rw_t ], locals', fx)
  | UTuple vs ->
      let* vs', locals', fx = r_list locals vs in
      ret (vs' @ [ Group (List.length vs) ], locals', fx)
  | Inj (i, v, t) ->
      let* types =
        match t with
        | Sum ts -> mapM ~f:(compile_type delta) ts
        | _ -> fail (InjNonSum t)
      in
      let* v', locals', fx = r v in
      ret (v' @ [ InjectNew (GC, i, types) ], locals', fx)
  | Pack (witness, v, _) ->
      let* v', locals', fx = r v in
      let* raw_t =
        match rw_t with
        | Exists (_, t) -> ret t
        | _ -> fail (PackNonExists rw_t)
      in
      let* witness' = compile_type delta witness in
      ret (v' @ [ Pack (Type witness', raw_t) ], locals', fx)
  | Var v ->
      (match
         List.find_map gamma ~f:(fun (name, t, i) ->
             Option.some_if (equal_string name v) (t, i))
       with
      | Some (t, idx) when contains_lin t ->
          (* lin values are uncopyable; move out and leave the plug behind, so
             richwasm rejects any second use *)
          ret ([ LocalGet (idx, Move) ], locals, [])
      | Some (_, idx) ->
          (* local.get sets the value to plug so we have to copy and put it back *)
          ret ([ LocalGet (idx, Move); Copy; LocalSet idx ], locals, [])
      | None -> fail (VarNotInGamma v))
  | Coderef (_, f) ->
      (match List.Assoc.find coderef_map ~equal:equal_string f with
      | Some idx -> ret ([ CodeRef idx ], locals, [])
      | None -> fail (CoderefNotFound f))
  | Op (o, left, right) ->
      let o' =
        Int.Binop.(
          match o with
          | `Add -> Add
          | `Sub -> Sub
          | `Mul -> Mul
          | `Div -> Div Signed)
      in
      let* left', locals', fx_l = r left in
      let* right', locals', fx_r =
        compile_expr delta gamma locals' coderef_map right
      in
      ret
        ( left' @ [ Untag ] @ right' @ [ Untag; Num (Int2 (I32, o')); Tag ],
          locals',
          fx_l @ fx_r )
  | Project (n, v) ->
      let* vt = type_of_e unindexed v in
      let* () =
        match vt with
        | Prod _ -> ret ()
        | UProd _ -> fail (ProjectUnboxed vt)
        | _ -> fail (ProjectNonProd vt)
      in
      let* v', locals', fx = r v in
      let temp_idx = List.length locals' in
      let locals'' = locals' @ [ ("#temp", rw_t) ] in
      let suffix =
        [
          Load (Path [ n ], Follow);
          LocalSet temp_idx;
          Drop;
          LocalGet (temp_idx, Move);
        ]
      in
      ret (v' @ suffix, locals'', fx @ [ (temp_idx, rw_t) ])
  | New v ->
      let* v', locals', fx = r v in
      ret (v' @ [ New (GC, Mut) ], locals', fx)
  | Deref v ->
      let* vt = type_of_e unindexed v in
      let* v', locals', fx = r v in
      (match vt with
      | Lin _ ->
          (* the copy-load leaves [ref; value]; pair them up unboxed *)
          ret (v' @ [ Load (Path [], Follow); Group 2 ], locals', fx)
      | _ ->
          let temp_idx = List.length locals' in
          let locals'' = locals' @ [ ("#temp", rw_t) ] in
          let suffix =
            [
              Load (Path [], Follow);
              LocalSet temp_idx;
              Drop;
              LocalGet (temp_idx, Move);
            ]
          in
          ret (v' @ suffix, locals'', fx @ [ (temp_idx, rw_t) ]))
  | Assign (re, v) ->
      (* NOTE: the store leaves the ref on the stack, which for lin is exactly
         the declared result *)
      let* re', locals', fx_re = r re in
      let* v', locals', fx_v = compile_expr delta gamma locals' coderef_map v in
      ret (re' @ v' @ [ Store (Path []) ], locals', fx_re @ fx_v)
  | Fold (_, v) ->
      (* NOTE: fold/unfold are pure retyping coercions (shared [Atom Ptr] rep); [Fold] takes the whole [Rec _]. *)
      let* () =
        match rw_t with
        | Rec _ -> ret ()
        | _ -> fail (FoldNonRec rw_t)
      in
      let* v', locals', fx = r v in
      ret (v' @ [ Fold rw_t ], locals', fx)
  | Unfold v ->
      let* v', locals', fx = r v in
      ret (v' @ [ Unfold ], locals', fx)
  | Apply (f, ts, arg) ->
      let* f', locals', fx_f = r f in
      let* arg', locals', fx_arg =
        compile_expr delta gamma locals' coderef_map arg
      in
      let* insts =
        mapM ts ~f:(fun t ->
            let+ t' = compile_type delta t in
            Inst (Type t'))
      in
      ret (arg' @ f' @ insts @ [ CallIndirect ], locals', fx_arg @ fx_f)
  | Unpack (var, (n, var_t), v, e) ->
      let* v', locals', fx_v = r v in
      let tmp_local = List.length locals' in
      let* tmp_local_t = compile_type (var :: delta) var_t in
      let* e', locals'', fx_e =
        compile_expr (var :: delta)
          ((n, var_t, tmp_local) :: gamma)
          (locals' @ [ ("#unpack-tmp", tmp_local_t) ])
          coderef_map e
      in
      let* inner_rw_t = compile_type (var :: delta) t in
      let fx = fx_v @ fx_e in
      let suffix =
        [
          Unpack
            ( ValType [ inner_rw_t ],
              InferFx,
              [ LocalSet tmp_local ] @ e' @ [ LocalGet (tmp_local, Move); Drop ]
            );
        ]
      in
      ret (v' @ suffix, locals'', fx)
  | Let ((n, t), e1, e2) ->
      let* e1', locals', fx1 = r e1 in
      let var_idx = List.length locals' in
      let* t' = compile_type delta t in
      let locals'' = locals' @ [ (n, t') ] in
      let* e2', locals''', fx2 =
        compile_expr delta ((n, t, var_idx) :: gamma) locals'' coderef_map e2
      in
      ret
        ( e1' @ [ LocalSet var_idx ] @ e2' @ [ LocalGet (var_idx, Move); Drop ],
          locals''',
          fx1 @ fx2 )
  | Split (bs, e1, e2) ->
      let* vt = type_of_e unindexed e1 in
      let* components =
        match vt with
        | UProd ts -> ret ts
        | _ -> fail (SplitNonUnboxed vt)
      in
      let binder_ts = List.map ~f:snd bs in
      let* () =
        if List.equal Closed.Type.equal binder_ts components then
          ret ()
        else
          fail (SplitMismatch (binder_ts, components))
      in
      let* e1', locals', fx1 = r e1 in
      let base_idx = List.length locals' in
      let* bound_locals =
        mapM bs ~f:(fun (n, t) ->
            let+ t' = compile_type delta t in
            (n, t'))
      in
      let gamma' =
        List.mapi bs ~f:(fun i (n, t) -> (n, t, base_idx + i)) @ gamma
      in
      let* e2', locals'', fx2 =
        compile_expr delta gamma' (locals' @ bound_locals) coderef_map e2
      in
      let idxs = List.mapi bs ~f:(fun i _ -> base_idx + i) in
      ret
        ( e1' @ [ Ungroup ]
          @ List.rev_map ~f:(fun i -> LocalSet i) idxs
          @ e2'
          @ List.concat_map ~f:(fun i -> [ LocalGet (i, Move); Drop ]) idxs,
          locals'',
          fx1 @ fx2 )
  | If0 (c, thn, els) ->
      let* c', locals', fx_c = r c in
      let* thn', locals', fx_t =
        compile_expr delta gamma locals' coderef_map thn
      in
      let* els', locals', fx_e =
        compile_expr delta gamma locals' coderef_map els
      in
      let suffix =
        [
          Untag;
          NumConst (Int I32, 0);
          Num (IntRel (I32, Eq));
          Ite (ValType [ rw_t ], InferFx, thn', els');
        ]
      in
      ret (c' @ suffix, locals', fx_c @ fx_t @ fx_e)
  | Cases (v, branches) ->
      let* v', locals', fx_v = r v in
      let* branches_rev, locals', fx =
        foldM
          ~f:(fun (branches', locals, fx) ((n, t), e) ->
            let new_local = List.length locals in
            let* t' = compile_type delta t in
            let* compiled, locals', fx' =
              compile_expr delta
                ((n, t, new_local) :: gamma)
                (locals @ [ (n, t') ])
                coderef_map e
            in
            let instrs =
              ((LocalSet new_local :: compiled)
              @ [ LocalGet (new_local, Move); Drop ])
              :: branches'
            in
            ret (instrs, locals', fx @ fx'))
          ~init:([], locals', []) branches
      in
      let branches' = List.rev branches_rev in
      let tmp_local = List.length locals' in
      let suffix =
        [
          CaseLoad (ValType [ rw_t ], Copy, InferFx, branches');
          LocalSet tmp_local;
          Drop;
          LocalGet (tmp_local, Move);
        ]
      in
      ret (v' @ suffix, locals' @ [ ("#cases-tmp", rw_t) ], fx_v @ fx)

let compile_fun coderef_map : Closed.Function.t -> Module.Function.t Res.t =
 fun (Function { name = _; foralls; arg = arg_name, arg_type; ret_type; body }) ->
  let open Res in
  let* arg_rw_type = compile_type foralls arg_type in
  let* ret_rw_type = compile_type foralls ret_type in
  let* body', locals, _ =
    compile_expr foralls
      [ (arg_name, arg_type, 0) ]
      [ (arg_name, arg_rw_type) ]
      coderef_map body
  in
  ret
    Module.Function.
      {
        typ =
          FunctionType
            ( List.map ~f:(Fn.const (Quantifier.Type kind)) foralls,
              [ arg_rw_type ],
              [ ret_rw_type ] );
        (* NOTE: declared locals come after the argument, whose slot the
           function type already accounts for *)
        locals = List.map ~f:(fun (_, t) -> rep_of_type t) (List.tl_exn locals);
        body = body' @ [ LocalGet (0, Move); Drop ];
      }

let compile_module (Closed.Module.Module (imps, fns, body)) : Module.t Res.t =
  let open Closed.PreType in
  let open Closed.Function in
  let open Res in
  let closed_unit = Prod [] in
  let* imports =
    mapM imps ~f:(fun (Import (_, t)) ->
        let* t' = compile_type [] t in
        match t' with
        | CodeRef ft -> ret ft
        | _ -> fail (ImportNotFunction t'))
  in
  let* fns =
    match body with
    | None -> ret fns
    | Some body ->
        let body_gamma =
          List.map ~f:(fun (Import (n, t)) -> (n, t)) imps
          @ List.map
              ~f:(fun (Export ((n, t), _) | Private ((n, t), _)) -> (n, t))
              fns
        in
        let* ret_type = type_of_e body_gamma body in
        ret
          (fns
          @ [
              Export
                ( ( "_start",
                    Code { foralls = []; arg = closed_unit; ret = ret_type } ),
                  Function
                    {
                      name = "_start";
                      foralls = [];
                      arg = ("#_env", closed_unit);
                      ret_type;
                      body;
                    } );
            ])
  in
  let import_offset = List.length imps in
  (* imports: 0..k-1, functions: k..k+n-1 *)
  let coderef_map =
    List.mapi ~f:(fun i (Import (n, _)) -> (n, i)) imps
    @ List.mapi
        ~f:(fun i -> function
          | Export ((n, _), _) | Private ((n, _), _) -> (n, import_offset + i))
        fns
  in
  let* functions =
    mapM
      ~f:(fun (Export (_, f) | Private (_, f)) -> compile_fun coderef_map f)
      fns
  in
  let exports =
    List.filter_mapi
      ~f:(fun i -> function
        | Export ((name, _), _) ->
            Some Module.Export.{ name; desc = Func (import_offset + i) }
        | Private _ -> None)
      fns
  in
  let table = List.init (import_offset + List.length fns) ~f:Fn.id in
  ret Module.{ imports; functions; table; exports }
