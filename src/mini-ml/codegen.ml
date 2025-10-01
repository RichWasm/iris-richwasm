open! Base
open Syntax
open Richwasm_common.Syntax

let rep = Representation.Prim PrimitiveRep.Ptr

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

and type_of_e gamma e =
  let open Closed.Expr in
  let open Closed.PreType in
  match e with
  | Value v -> type_of_v gamma v
  | Apply (f, ts, _) -> (
      match type_of_v gamma f with
      | Exists (_, Prod [ _; Code { foralls; ret; _ } ]) ->
          List.fold_right2_exn ~init:ret ~f:type_subst foralls ts
      | _ -> failwith "application should be on a existential/closure")
  | Project (i, v) -> (
      match type_of_v gamma v with
      | Prod ts -> List.nth_exn ts i
      | _ -> failwith "projection should be on a product")
  | Op _ -> Int
  | If0 (_, e, _) -> type_of_e gamma e
  | Cases (_, ((n, t), e) :: _) -> type_of_e ((n, t) :: gamma) e
  | Cases _ -> failwith "no empty cases"
  | New v -> Ref (type_of_v gamma v)
  | Deref v -> (
      match type_of_v gamma v with
      | Ref t -> t
      | _ -> failwith "deref should be on a ref")
  | Assign _ -> Prod []
  | Let ((n, t), _, e) -> type_of_e ((n, t) :: gamma) e
  | Fold (t, _) -> t
  | Unfold v -> (
      match type_of_v gamma v with
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
      Type.(Ref (GC, Prod ts'))
  | Sum ts ->
      let ts' = List.map ~f:(fun x -> Type.Ser (r x)) ts in
      Type.(Ref (GC, Sum ts'))
  | Ref t -> Type.(Ref (GC, Ser (r t)))
  | Rec (v, t) -> Type.Rec (compile_type (v :: delta) t)
  | Exists (v, t) ->
      Type.(
        Ref (GC, Exists (Quantifier.Type kind, compile_type (v :: delta) t)))
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
  let r = compile_value delta gamma locals functions in
  let t = type_of_v gamma v in
  let rw_t = compile_type delta t in
  let box = [ RefNew (Memory.GC, rw_t); RefStore (Path []) ] in
  match v with
  | Int i ->
      let open NumType in
      [ NumConst (Int I32, i); Tag ]
  | Tuple vs ->
      let items = List.concat_map ~f:r vs in
      items @ [ Group (List.length vs) ] @ box
  | Inj (i, v, t) ->
      let types =
        match t with
        | Closed.PreType.Sum ts -> List.map ~f:(compile_type delta) ts
        | _ -> failwith "inj should be annotated with sum type"
      in
      r v @ [ Inject (i, types) ] @ box
  | Pack (witness, v, _) ->
      r v @ [ Pack (Index.Type (compile_type delta witness), rw_t) ] @ box
  | Fun _ -> failwith "functions should be compiled with [compile_fun]"
  | Var v ->
      let idx =
        List.find_mapi_exn
          ~f:(fun i (name, _) -> Option.some_if (equal_string name v) i)
          locals
      in
      [ LocalGet idx ]

and compile_expr delta gamma locals functions e =
  let open Closed.Expr in
  let open Closed.Value in
  let open Instruction in
  let open InstructionType in
  let open LocalFx in
  let cv = compile_value delta gamma locals functions in
  let r = compile_expr delta gamma locals functions in
  let t = type_of_e gamma e in
  let rw_t = compile_type delta t in
  match e with
  | Value v -> (cv v, locals)
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
        locals )
  | Project (n, v) ->
      (* FIXME: is this the whole product type or the type of projected field *)
      (cv v @ [ RefLoad (Path.Path [ Path.Component.Proj n ], rw_t) ], locals)
  | New v -> (cv v @ [ RefNew (Memory.GC, rw_t) ], locals)
  | Deref v -> (cv v @ [ RefLoad (Path.Path [], rw_t) ], locals)
  | Assign (r, v) -> (cv r @ cv v @ [ RefStore (Path.Path []) ], locals)
  | Fold (_, v) -> (cv v @ [ Fold rw_t ], locals)
  | Unfold v -> (cv v @ [ Unfold ], locals)
  | Unpack (var, (n, t), v, e) ->
      ( cv v
        @ [
            RefLoad (Path.Path [], compile_type delta t);
            Unpack
              ( InstructionType
                  ([ type_of_v gamma v |> compile_type delta ], [ rw_t ]),
                LocalFx [],
                (* TODO: what about these locals?
                   should they make it to function locals? *)
                compile_expr (var :: delta) ((n, t) :: gamma)
                  (locals @ [ (n, compile_type delta t) ])
                  functions e
                |> fst );
          ],
        locals )
  | Let ((n, t), e1, e2) ->
      let e1', locals' = r e1 in
      let locals' = locals' @ [ (n, compile_type delta t) ] in
      ( e1'
        @ [ LocalSet (List.length locals) ]
        @ (compile_expr delta ((n, t) :: gamma) locals' functions e2 |> fst),
        locals' )
  | If0 (c, thn, els) ->
      let thn', locals' = r thn in
      let els', locals' = compile_expr delta gamma locals' functions els in
      ( cv c
        @ [
            Untag;
            Ite
              ( InstructionType
                  ([ Type.Num (NumType.Int Int.Type.I32) ], [ rw_t ]),
                LocalFx [],
                thn',
                els' );
          ],
        locals' )
  | Cases (v, branches) ->
      let branches', locals' =
        List.fold_left branches
          ~f:(fun (branches', locals) ((n, t), e) ->
            let compiled, locals' =
              compile_expr delta ((n, t) :: gamma)
                (locals @ [ (n, compile_type delta t) ])
                functions e
            in
            let bound_local_idx = List.length locals' - 1 in
            ((LocalSet bound_local_idx :: compiled) :: branches', locals'))
          ~init:([], locals)
      in
      ( cv v
        @ [
            Case
              ( InstructionType
                  ([ v |> type_of_v gamma |> compile_type delta ], [ rw_t ]),
                LocalFx [],
                branches' );
          ],
        locals' )
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
        locals )

let compile_fun
    functions
    (Closed.Value.Fun { foralls; arg = (_, arg_type) as arg; ret_type; body }) :
    Module.Function.t =
  let open FunctionType in
  let open Type in
  let body', locals = compile_expr foralls [ arg ] [] functions body in
  {
    typ =
      FunctionType
        ( List.map ~f:(Fn.const (Quantifier.Type kind)) foralls,
          [ compile_type foralls arg_type ],
          [ compile_type foralls ret_type ] );
    locals = List.map ~f:(Fn.const rep) locals;
    body = body';
  }
