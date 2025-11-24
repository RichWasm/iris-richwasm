open! Base
open Syntax
open Richwasm_common.Syntax

let rep = Representation.Atom AtomicRep.Ptr

let kind =
  (* the kind of all mini-ml types: [VALTYPE ptr ExCopy ExDrop] *)
  Kind.VALTYPE (rep, Copyability.ExCopy, Dropability.ExDrop)

let rec type_subst var replacement tau =
  let open Closed.PreType in
  match tau with
  | Int -> Int
  | Prod ts -> Prod (List.map ~f:(type_subst var replacement) ts)
  | Sum ts -> Sum (List.map ~f:(type_subst var replacement) ts)
  | Ref t -> Ref (type_subst var replacement t)
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

let rec type_of_e gamma e =
  let open Closed.Expr in
  let open Closed.PreType in
  match e with
  | Inj (_, _, t) | Pack (_, _, t) | Coderef (t, _) -> t
  | Int _ -> Int
  | Tuple vs -> Prod (List.map ~f:(type_of_e gamma) vs)
  | Var v ->
      (try List.Assoc.find_exn ~equal:equal_string gamma v
       with Not_found_s _ -> failwith ("unbound variable: " ^ v))
  | Apply (f, ts, _) ->
      (match type_of_e gamma f with
      | Exists (_, Prod [ _; Code { foralls; ret; _ } ]) ->
          List.fold_right2_exn ~init:ret ~f:type_subst foralls ts
      | t ->
          failwith
            ("application should be on a closure, got: "
            ^ Sexp.to_string (Closed.PreType.sexp_of_t t)
            ^ "\nexpression: "
            ^ Sexp.to_string (Closed.Expr.sexp_of_t e)))
  | Project (i, v) ->
      (match type_of_e gamma v with
      | Prod ts -> List.nth_exn ts i
      | _ -> failwith "projection should be on a product")
  | Op _ -> Int
  | If0 (_, e, _) -> type_of_e gamma e
  | Cases (_, ((n, t), e) :: _) -> type_of_e ((n, t) :: gamma) e
  | Cases _ -> failwith "no empty cases"
  | New v -> Ref (type_of_e gamma v)
  | Deref v ->
      (match type_of_e gamma v with
      | Ref t -> t
      | _ -> failwith "deref should be on a ref")
  | Assign _ -> Prod []
  | Let ((n, t), _, e) -> type_of_e ((n, t) :: gamma) e
  | Fold (t, _) -> t
  | Unfold v ->
      (match type_of_e gamma v with
      | Rec (var, t) as tau -> type_subst var tau t
      | _ -> failwith "unfold should be on a µ-type")
  | Unpack (_, (n, t), _, e) -> type_of_e ((n, t) :: gamma) e

let rec compile_type delta t =
  let open Closed.PreType in
  let open Memory in
  let r = compile_type delta in
  match t with
  | Int -> Type.I31
  | Prod ts ->
      let ts' = List.map ~f:(fun x -> Type.Ser (r x)) ts in
      Type.(Ref (Base GC, Ser (Prod ts')))
  | Sum ts ->
      let ts' = List.map ~f:(fun x -> Type.Ser (r x)) ts in
      Type.(Ref (Base GC, Ser (Sum ts')))
  | Ref t -> Type.(Ref (Base GC, Ser (r t)))
  | Rec (v, t) -> Type.Rec (kind, compile_type (v :: delta) t)
  | Exists (v, t) ->
      Type.(
        Ref
          ( Base GC,
            Ser (Exists (Quantifier.Type kind, compile_type (v :: delta) t)) ))
  | Code { foralls; arg; ret } ->
      let r = compile_type (foralls @ delta) in
      Type.CodeRef
        (FunctionType.FunctionType
           ( List.map ~f:(Fn.const (Quantifier.Type kind)) foralls,
             [ r arg ],
             [ r ret ] ))
  | Var v ->
      delta
      |> List.find_mapi_exn ~f:(fun i name ->
          Option.some_if (equal_string name v) i)
      |> fun x -> Type.Var x

let rec compile_expr delta gamma locals functions e =
  let open Closed.Expr in
  let open Instruction in
  let open BlockType in
  let open LocalFx in
  let unindexed = List.map ~f:(fun (n, t, _) -> (n, t)) gamma in
  let r = compile_expr delta gamma locals functions in
  let t = type_of_e unindexed e in
  let rw_t = compile_type delta t in
  let new_local_idx = List.length locals in
  let rw_unit = Type.Prod [] in
  match e with
  | Int i ->
      let open NumType in
      ([ NumConst (Int I32, i); Tag ], locals, [])
  | Tuple vs ->
      let vs', locals', fx =
        List.fold_left
          ~f:(fun (instrs, locals, fx) item ->
            let v', locals', fx' =
              compile_expr delta gamma locals functions item
            in
            (instrs @ v', locals', fx @ fx'))
          ~init:([], locals, []) vs
      in
      (vs' @ [ Group (List.length vs); New GC ], locals', fx)
  | Inj (i, v, t) ->
      let types =
        match t with
        | Closed.PreType.Sum ts -> List.map ~f:(compile_type delta) ts
        | _ -> failwith "inj should be annotated with sum type"
      in
      let v', locals', fx = r v in
      (v' @ [ Inject (Some GC, i, types) ], locals', fx)
  | Pack (witness, v, _) ->
      let v', locals', fx = r v in
      ( v' @ [ Pack (Index.Type (compile_type delta witness), rw_t); New GC ],
        locals',
        fx )
  | Var v ->
      let idx =
        List.find_map_exn
          ~f:(fun (name, _, i) -> Option.some_if (equal_string name v) i)
          gamma
      in
      (* local.get sets the value to unit, so we have to copy and put it back *)
      ([ LocalGet (idx, Move); Copy; LocalSet idx ], locals, [])
  | Coderef (_, f) ->
      let idx =
        List.find_mapi_exn
          ~f:(fun i -> function
            | Closed.Function.Function { name; _ } ->
                Option.some_if (equal_string name f) i)
          functions
      in
      ([ CodeRef idx ], locals, [])
  | Op (o, left, right) ->
      let o' =
        Int.Binop.(
          match o with
          | `Add -> Add
          | `Sub -> Sub
          | `Mul -> Mul
          | `Div -> Div Sign.Signed)
      in
      let left', locals', fx_l = r left in
      let right', locals', fx_r =
        compile_expr delta gamma locals' functions right
      in
      ( left' @ [ Untag ] @ right'
        @ [ Untag; Num (NumInstruction.Int2 (Int.Type.I32, o')); Tag ],
        locals',
        fx_l @ fx_r )
  | Project (n, v) ->
      let v', locals', fx = r v in
      (v' @ [ Load (Path.Path [ n ], Follow) ], locals', fx)
  | New v ->
      let v', locals', fx = r v in
      (v' @ [ New BaseMemory.GC ], locals', fx)
  | Deref v ->
      let v', locals', fx = r v in
      (v' @ [ Load (Path.Path [], Follow) ], locals', fx)
  | Assign (re, v) ->
      let re', locals', fx_re = r re in
      let v', locals', fx_v = compile_expr delta gamma locals' functions v in
      (re' @ v' @ [ Store (Path.Path []) ], locals', fx_re @ fx_v)
  | Fold (_, v) ->
      let v', locals', fx = r v in
      (v' @ [ Fold rw_t ], locals', fx)
  | Unfold v ->
      let v', locals', fx = r v in
      (v' @ [ Unfold ], locals', fx)
  | Apply (f, _, arg) ->
      let f', locals', fx_f = r f in
      let arg', locals', fx_arg =
        compile_expr delta gamma locals' functions arg
      in
      (* FIXME: figure out why [Inst] only takes one index *)
      (arg' @ f' @ [ CallIndirect ], locals', fx_arg @ fx_f)
  | Unpack (var, (n, t), v, e) ->
      let v', locals', fx_v = r v in
      let e', locals', fx_e =
        compile_expr (var :: delta)
          ((n, t, new_local_idx) :: gamma)
          (locals' @ [ (n, compile_type (var :: delta) t) ])
          functions e
      in
      let fx = fx_v @ fx_e @ [ (new_local_idx, rw_unit) ] in
      ( v'
        @ [
            Load (Path.Path [], Follow);
            Unpack
              ( ArrowType (1, [ rw_t ]),
                LocalFx fx,
                [ LocalSet new_local_idx ] @ e'
                @ [ LocalGet (new_local_idx, Move); Drop ] );
          ],
        locals',
        fx )
  | Let ((n, t), e1, e2) ->
      let e1', locals', fx1 = r e1 in
      let locals' = locals' @ [ (n, compile_type delta t) ] in
      let e2', locals', fx2 =
        compile_expr delta ((n, t, new_local_idx) :: gamma) locals' functions e2
      in
      ( e1' @ [ LocalSet new_local_idx ] @ e2'
        @ [ LocalGet (new_local_idx, Move); Drop ],
        locals',
        fx1 @ fx2 )
  | If0 (c, thn, els) ->
      let c', locals', fx_c = r c in
      let thn', locals', fx_t =
        compile_expr delta gamma locals' functions thn
      in
      let els', locals', fx_e =
        compile_expr delta gamma locals' functions els
      in
      ( c'
        @ [
            Untag;
            Ite (ArrowType (1, [ rw_t ]), LocalFx (fx_t @ fx_e), thn', els');
          ],
        locals',
        fx_c @ fx_t @ fx_e )
  | Cases (v, branches) ->
      let v', locals', fx_v = r v in
      let branches', locals', fx =
        List.fold_left branches
          ~f:(fun (branches', locals, fx) ((n, t), e) ->
            let new_local = List.length locals in
            let compiled, locals', fx' =
              compile_expr delta
                ((n, t, new_local) :: gamma)
                (locals @ [ (n, compile_type delta t) ])
                functions e
            in
            ( ((LocalSet new_local :: compiled)
              @ [ LocalGet (new_local, Move); Drop ])
              :: branches',
              locals',
              fx @ fx' ))
          ~init:([], locals', [])
      in
      ( v' @ [ Case (ArrowType (1, [ rw_t ]), LocalFx fx, branches') ],
        locals',
        fx_v @ fx )

let compile_fun functions : Closed.Function.t -> Module.Function.t = function
  | Closed.Function.Function
      { name = _; foralls; arg = arg_name, arg_type; ret_type; body } ->
      let open FunctionType in
      let arg_rw_type = compile_type foralls arg_type in
      let ret_rw_type = compile_type foralls ret_type in
      let body', locals, _ =
        compile_expr foralls
          [ (arg_name, arg_type, 0) ]
          [ (arg_name, arg_rw_type) ]
          functions body
      in
      {
        typ =
          FunctionType
            ( List.map ~f:(Fn.const (Quantifier.Type kind)) foralls,
              [ arg_rw_type ],
              [ ret_rw_type ] );
        locals = List.map ~f:(Fn.const rep) locals;
        body = body';
      }

let compile_module (Closed.Module.Module (imps, fns, body)) : Module.t =
  let open Closed.Module in
  let open Closed.PreType in
  let open Closed.Function in
  let closed_unit = Prod [] in
  let imports =
    List.map
      ~f:(fun (Import (_, t)) ->
        match compile_type [] t with
        | Type.CodeRef ft -> ft
        | _ -> failwith "imports must be functions")
      imps
  in
  let fns =
    match body with
    | None -> fns
    | Some body ->
        fns
        @ [
            Export
              ( ( "_start",
                  Code { foralls = []; arg = closed_unit; ret = closed_unit } ),
                Function
                  {
                    name = "_start";
                    foralls = [];
                    arg = ("#_env", closed_unit);
                    ret_type = closed_unit;
                    body;
                  } );
          ]
  in
  let functions =
    List.map
      ~f:(function
        | Export (_, f) | Private (_, f) -> f)
      fns
  in
  let functions =
    List.map
      ~f:(function
        | Export (_, f) | Private (_, f) -> compile_fun functions f)
      fns
  in
  let exports =
    List.filter_mapi
      ~f:(fun i -> function
        | Export _ -> Some i
        | Private _ -> None)
      fns
  in
  { imports; functions; table = []; exports }
