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

let rec type_of_v gamma v =
  let open Closed in
  match v with
  | Value.Int _ -> PreType.Int
  | Value.Tuple vs -> PreType.Prod (List.map ~f:(type_of_v gamma) vs)
  | Value.Inj (_, _, t) -> t
  | Value.Pack (_, _, t) -> t
  | Value.Fun { foralls; arg = _, t; ret_type; _ } ->
      PreType.Code { foralls; arg = t; ret = ret_type }
  | Value.Var v -> List.Assoc.find_exn ~equal:equal_string gamma v

let rec type_of_e gamma e =
  let open Closed.Expr in
  let open Closed.PreType in
  match e with
  | Value v -> type_of_v gamma v
  | Apply (f, ts, _) ->
      (match type_of_v gamma f with
      | Exists (_, Prod [ _; Code { foralls; ret; _ } ]) ->
          List.fold_right2_exn ~init:ret ~f:type_subst foralls ts
      | _ -> failwith "application should be on a existential/closure")
  | Project (i, v) ->
      (match type_of_v gamma v with
      | Prod ts -> List.nth_exn ts i
      | _ -> failwith "projection should be on a product")
  | Op _ -> Int
  | If0 (_, e, _) -> type_of_e gamma e
  | Cases (_, ((n, t), e) :: _) -> type_of_e ((n, t) :: gamma) e
  | Cases _ -> failwith "no empty cases"
  | New v -> Ref (type_of_v gamma v)
  | Deref v ->
      (match type_of_v gamma v with
      | Ref t -> t
      | _ -> failwith "deref should be on a ref")
  | Assign _ -> Prod []
  | Let ((n, t), _, e) -> type_of_e ((n, t) :: gamma) e
  | Fold (t, _) -> t
  | Unfold v ->
      (match type_of_v gamma v with
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
      Type.(Ref (Base GC, Prod ts'))
  | Sum ts ->
      let ts' = List.map ~f:(fun x -> Type.Ser (r x)) ts in
      Type.(Ref (Base GC, Sum ts'))
  | Ref t -> Type.(Ref (Base GC, Ser (r t)))
  | Rec (v, t) -> Type.Rec (kind, compile_type (v :: delta) t)
  | Exists (v, t) ->
      Type.(
        Ref (Base GC, Exists (Quantifier.Type kind, compile_type (v :: delta) t)))
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

let rec compile_value delta gamma locals functions v =
  let open Closed.Value in
  let open Instruction in
  let unindexed = List.map ~f:(fun (n, t, _) -> (n, t)) gamma in
  let r = compile_value delta gamma locals functions in
  let t = type_of_v unindexed v in
  let rw_t = compile_type delta t in
  match v with
  | Int i ->
      let open NumType in
      [ NumConst (Int I32, i); Tag ]
  | Tuple vs ->
      let items = List.concat_map ~f:r vs in
      items @ [ Group (List.length vs); New GC ]
  | Inj (i, v, t) ->
      let types =
        match t with
        | Closed.PreType.Sum ts -> List.map ~f:(compile_type delta) ts
        | _ -> failwith "inj should be annotated with sum type"
      in
      r v @ [ Inject (Some GC, i, types) ]
  | Pack (witness, v, _) ->
      r v @ [ Pack (Index.Type (compile_type delta witness), rw_t); New GC ]
  | Fun _ -> failwith "functions should be compiled with [compile_fun]"
  | Var v ->
      let idx =
        List.find_map_exn
          ~f:(fun (name, _, i) -> Option.some_if (equal_string name v) i)
          gamma
      in
      (* local.get sets the value to unit, so we have to copy and put it back *)
      [ LocalGet (idx, Move); Copy; LocalSet idx ]

let rec compile_expr delta gamma locals functions e =
  let open Closed.Expr in
  let open Instruction in
  let open BlockType in
  let open LocalFx in
  let unindexed = List.map ~f:(fun (n, t, _) -> (n, t)) gamma in
  let cv = compile_value delta gamma locals functions in
  let r = compile_expr delta gamma locals functions in
  let t = type_of_e unindexed e in
  let rw_t = compile_type delta t in
  let new_local_idx = List.length locals in
  let rw_unit = Type.Prod [] in
  match e with
  | Value v -> (cv v, locals, [])
  | Op (o, l, r) ->
      let o' =
        Int.Binop.(
          match o with
          | `Add -> Add
          | `Sub -> Sub
          | `Mul -> Mul
          | `Div -> Div Sign.Signed)
      in
      ( cv l
        @ [ Untag ]
        @ cv r
        @ [ Untag; Num (NumInstruction.Int2 (Int.Type.I32, o')); Tag ],
        locals,
        [] )
  | Project (n, v) -> (cv v @ [ Load (Path.Path [ n ], Follow) ], locals, [])
  | New v -> (cv v @ [ New BaseMemory.GC ], locals, [])
  | Deref v -> (cv v @ [ Load (Path.Path [], Follow) ], locals, [])
  | Assign (r, v) -> (cv r @ cv v @ [ Store (Path.Path []) ], locals, [])
  | Fold (_, v) -> (cv v @ [ Fold rw_t ], locals, [])
  | Unfold v -> (cv v @ [ Unfold ], locals, [])
  | Unpack (var, (n, t), v, e) ->
      let e', locals', fx =
        compile_expr (var :: delta)
          ((n, t, new_local_idx) :: gamma)
          (locals @ [ (n, compile_type delta t) ])
          functions e
      in
      let fx = fx @ [ (new_local_idx, rw_unit) ] in
      ( cv v
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
      let thn', locals', fx_t = r thn in
      let els', locals', fx_e =
        compile_expr delta gamma locals' functions els
      in
      ( cv c
        @ [
            Untag;
            Ite (ArrowType (1, [ rw_t ]), LocalFx (fx_t @ fx_e), thn', els');
          ],
        locals',
        fx_t @ fx_e )
  | Cases (v, branches) ->
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
          ~init:([], locals, [])
      in
      ( cv v @ [ Case (ArrowType (1, [ rw_t ]), LocalFx fx, branches') ],
        locals',
        fx )
  | Apply (f, ts, arg) ->
      let fn_name =
        match f with
        | Closed.Value.Var v -> v
        | _ -> failwith "apply must be on a function name"
      in
      let fn_idx =
        List.find_mapi_exn
          ~f:(fun i (n, _) -> Option.some_if (equal_string n fn_name) i)
          functions
      in
      ( cv f
        @ cv arg
        @ [
            Call
              ( fn_idx,
                List.map ~f:(fun t -> Index.Type (compile_type delta t)) ts );
          ],
        locals,
        [] )

let[@warning "-8"] compile_fun
    functions
    (Closed.Value.Fun { foralls; arg = arg_name, arg_type; ret_type; body }) :
    Module.Function.t =
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
  let open Closed.Expr in
  let open Closed.PreType in
  let open Closed.Value in
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
                Value
                  (Fun
                     {
                       foralls = [];
                       arg = ("_", closed_unit);
                       ret_type = closed_unit;
                       body;
                     }) );
          ]
  in
  let functions =
    List.map
      ~f:(function
        | Export ((n, t), _) | Private ((n, t), _) -> (n, t))
      fns
  in
  let functions =
    (* FIXME: update source syntax to make sure these are always functions
     *  (or at least values) *)
    List.map
      ~f:(function
        | Export (_, Value v) | Private (_, Value v) -> compile_fun functions v
        | _ -> failwith "expected function value here")
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
