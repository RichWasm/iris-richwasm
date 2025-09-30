open! Base
open Syntax
open Richwasm_common.Syntax

let kind =
  (* the kind of all mini-ml types: [VALTYPE ptr ExCopy ExDrop] *)
  Kind.VALTYPE
    ( Representation.Prim PrimitiveRep.Ptr,
      Copyability.ExCopy,
      Dropability.ExDrop )

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

let rec compile_value delta gamma locals globals v =
  let open Closed.Value in
  let open Instruction in
  let r = compile_value delta gamma locals globals in
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
  | Fun { foralls; arg; ret_type; body } -> failwith "todo"
  | Var v ->
      let idx =
        List.find_mapi_exn
          ~f:(fun i (name, _) -> Option.some_if (equal_string name v) i)
          locals
      in
      [ LocalGet idx ]

and compile_expr delta gamma locals globals e =
  let open Closed.Expr in
  let open Closed.Value in
  let open Instruction in
  let open InstructionType in
  let open LocalFx in
  let cv = compile_value delta gamma locals globals in
  let r = compile_expr delta gamma locals globals in
  let t = type_of_e gamma e in
  let rw_t = compile_type delta t in
  match e with
  | Value v -> cv v
  | Op (o, l, r) ->
      let o' =
        Int.Binop.(
          match o with
          | `Add -> Add
          | `Sub -> Sub
          | `Mul -> Mul
          | `Div -> Div Sign.Signed)
      in
      cv l
      @ [ Untag ]
      @ cv r
      @ [ Untag; Num (NumInstruction.Int2 (Int.Type.I32, o')); Tag ]
  | Project (n, v) ->
      (* FIXME: is this the whole product type or the type of projected field *)
      cv v @ [ RefLoad (Path.Path [ Path.Component.Proj n ], rw_t) ]
  | New v -> cv v @ [ RefNew (Memory.GC, rw_t) ]
  | Deref v -> cv v @ [ RefLoad (Path.Path [], rw_t) ]
  | Assign (r, v) -> cv r @ cv v @ [ RefStore (Path.Path []) ]
  | Fold (_, v) -> cv v @ [ Fold rw_t ]
  | Unfold v -> cv v @ [ Unfold ]
  | Unpack (var, (n, t), v, e) ->
      cv v
      @ [
          RefLoad (Path.Path [], compile_type delta t);
          Unpack
            ( InstructionType
                ([ type_of_v gamma v |> compile_type delta ], [ rw_t ]),
              LocalFx [],
              compile_expr (var :: delta) ((n, t) :: gamma)
                (locals @ [ (n, compile_type delta t) ])
                globals e );
        ]
  | Let ((n, t), e1, e2) ->
      r e1
      @ [ LocalSet (List.length locals) ]
      @ compile_expr delta ((n, t) :: gamma)
          (locals @ [ (n, compile_type delta t) ])
          globals e2
  | If0 (c, thn, els) ->
      cv c
      @ [
          Untag;
          Ite
            ( InstructionType ([ Type.Num (NumType.Int Int.Type.I32) ], [ rw_t ]),
              LocalFx [],
              r thn,
              r els );
        ]
  | Cases (v, branches) ->
      cv v
      @ [
          Case
            ( InstructionType
                ([ type_of_v gamma v |> compile_type delta ], [ rw_t ]),
              LocalFx [],
              List.map
                ~f:(fun ((n, t), e) ->
                  compile_expr delta ((n, t) :: gamma)
                    (locals @ [ (n, compile_type delta t) ])
                    globals e)
                branches );
        ]
  | _ -> failwith "todoo"
