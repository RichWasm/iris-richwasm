open! Base
open Syntax

let rec fv ?(bound = []) (e : Source.Expr.t) : Source.Variable.t list =
  let open Source.Expr in
  let fe = fv ~bound in
  match e with
  | Int _ -> []
  | Var v ->
      if List.mem ~equal:equal_string bound v then
        []
      else
        [ v ]
  | Tuple vs -> List.concat_map ~f:fv vs
  | Inj (_, v, _) -> fv v
  | Fun { arg = n, _; body; _ } -> fv ~bound:(n :: bound) body
  | Apply (f, _, arg) -> fe f @ fe arg
  | Project (_, v) -> fe v
  | Op (_, l, r) -> fe l @ fe r
  | If0 (c, t, e) -> fe c @ fe t @ fe e
  | New v -> fe v
  | Deref v -> fe v
  | Assign (r, v) -> fe r @ fe v
  | Fold (_, v) -> fe v
  | Unfold v -> fe v
  | Let ((n, _), e1, e2) -> fe e1 @ fv ~bound:(n :: bound) e2
  | Cases (v, branches) ->
      fe v
      @ List.concat_map
          ~f:(fun ((n, _), e) -> fv ~bound:(n :: bound) e)
          branches

let rec ftv ?(bound = []) (t : Source.Type.t) : Source.Variable.t list =
  let ftv_pt pt =
    let open Source.PreType in
    match pt with
    | Int -> []
    | Var v ->
        if List.mem ~equal:equal_string bound v then
          []
        else
          [ v ]
    | Prod ts -> List.concat_map ~f:(ftv ~bound) ts
    | Sum ts -> List.concat_map ~f:(ftv ~bound) ts
    | Ref t -> ftv ~bound t
    | Rec (v, t) -> ftv ~bound:(v :: bound) t
    | Fun { foralls; arg; ret } ->
        let bound = foralls @ bound in
        ftv ~bound arg @ ftv ~bound ret
  in
  ftv_pt t

let rec ftv_e ?(bound = []) (e : Source.Expr.t) : Source.Variable.t list =
  let open Source.Expr in
  let r = ftv_e ~bound in
  match e with
  | Inj (_, _, t) -> ftv ~bound t
  | Fun { foralls; arg = _, t; ret_type; body } ->
      (* TODO: do both of these have to be here? *)
      ftv (Fun { foralls; arg = t; ret = ret_type }) @ ftv_e ~bound:foralls body
  | Int _ | Var _ | Tuple _ -> []
  | Apply (f, ts, arg) -> r f @ List.concat_map ~f:(ftv ~bound) ts @ r arg
  | Project (_, v) -> r v
  | Op (_, left, right) -> r left @ r right
  | If0 (c, t, e) -> r c @ r t @ r e
  | Cases (v, branches) ->
      r v @ (branches |> List.unzip |> snd |> List.concat_map ~f:(ftv_e ~bound))
  | New v -> r v
  | Deref v -> r v
  | Assign (re, v) -> r re @ r v
  | Let (_, e1, e2) -> r e1 @ r e2
  | Fold (_, v) -> r v
  | Unfold v -> r v

let rec cc_t t = cc_pt t

and cc_pt pt =
  match pt with
  | Source.PreType.Int -> Closed.PreType.Int
  | Source.PreType.Var v -> Closed.PreType.Var v
  | Source.PreType.Prod ts -> Closed.PreType.Prod (List.map ~f:cc_t ts)
  | Source.PreType.Sum ts -> Closed.PreType.Sum (List.map ~f:cc_t ts)
  | Source.PreType.Ref t -> Closed.PreType.Ref (cc_t t)
  | Source.PreType.Rec (v, t) -> Closed.PreType.Rec (v, cc_t t)
  | Source.PreType.Fun { foralls; arg; ret } ->
      Closed.(
        PreType.Exists
          ( "#cc-env",
            PreType.Prod
              [
                PreType.Var "#cc-env";
                PreType.Code
                  {
                    foralls;
                    arg = PreType.Prod [ PreType.Var "#cc-env"; cc_t arg ];
                    ret = cc_t ret;
                  };
              ] ))

let rec cc_e user_fns gamma tagger acc e =
  let open Source.Expr in
  let r = cc_e user_fns gamma tagger in
  match e with
  | Int i -> (Closed.Expr.Int i, acc)
  | Var v ->
      (match List.Assoc.find ~equal:equal_string user_fns v with
      (* manually pack user-written/imported function *)
      | Some t ->
          ( Closed.(
              Expr.Pack
                ( PreType.Prod [],
                  Expr.Tuple [ Expr.Tuple []; Expr.Coderef (cc_t t, v) ],
                  cc_t t )),
            acc )
      | None -> (Closed.Expr.Var v, acc))
  | Tuple vs ->
      let vs, code =
        List.fold_left
          ~f:(fun (vs, extra) v ->
            let converted, code = r acc v in
            (converted :: vs, code @ extra))
          ~init:([], acc) vs
      in
      (Closed.Expr.Tuple vs, code)
  | Inj (i, v, t) ->
      let v, code = r acc v in
      (Closed.Expr.Inj (i, v, cc_t t), code)
  | Fun { foralls; arg = (n, t) as arg; ret_type; body } ->
      let gamma = arg :: gamma in
      let free_vars = fv body in
      let free_type_vars = ftv_e body in
      let closure_id = Int.to_string (tagger ()) in
      let code_name = "closure#fn" ^ closure_id in
      let cced_body, code = cc_e user_fns gamma tagger acc body in
      let env_type =
        free_vars
        |> List.map ~f:(List.Assoc.find_exn ~equal:equal_string gamma)
        |> List.map ~f:cc_t
      in
      let env_prod = Closed.PreType.Prod env_type in
      let free_bindings = List.zip_exn free_vars env_type in
      let function_type =
        Closed.PreType.Code
          {
            foralls = free_type_vars @ foralls;
            arg = Closed.PreType.Prod [ env_prod; cc_t t ];
            ret = cc_t ret_type;
          }
      in
      Closed.
        ( Expr.Pack
            ( env_prod,
              Expr.Tuple
                [
                  Expr.Tuple (List.map ~f:(fun v -> Expr.Var v) free_vars);
                  Expr.Coderef (function_type, code_name);
                ],
              PreType.Exists ("#cc-env", function_type) ),
          Function.Function
            {
              name = code_name;
              foralls = free_type_vars @ foralls;
              arg = ("#env_and_arg", PreType.Prod [ env_prod; cc_t t ]);
              ret_type = cc_t ret_type;
              body =
                Expr.Let
                  ( ("#env", env_prod),
                    Expr.Project (0, Expr.Var "#env_and_arg"),
                    Expr.Let
                      ( (n, cc_t t),
                        Expr.Project (1, Expr.Var "#env_and_arg"),
                        List.fold_right
                          ~f:(fun (idx, (name, ty)) acc ->
                            Expr.Let
                              ( (name, ty),
                                Expr.Project (idx, Expr.Var "#env"),
                                acc ))
                          ~init:cced_body
                          (List.zip_exn
                             (List.range 0 (List.length free_bindings))
                             free_bindings) ) );
            }
          :: code )
  | Project (i, v) ->
      let v', code = r acc v in
      (Closed.Expr.Project (i, v'), code)
  | Op (o, left, right) ->
      let l', acc' = r acc left in
      let r', code = r acc' right in
      (Closed.Expr.Op (o, l', r'), code)
  | New v ->
      let v', code = r acc v in
      (Closed.Expr.New v', code)
  | Deref v ->
      let v', code = r acc v in
      (Closed.Expr.Deref v', code)
  | Assign (re, v) ->
      let r', acc' = r acc re in
      let v', code = r acc' v in
      (Closed.Expr.Assign (r', v'), code)
  | Fold (t, v) ->
      let t' = cc_t t in
      let v', code = r acc v in
      (Closed.Expr.Fold (t', v'), code)
  | Unfold v ->
      let v', code = r acc v in
      (Closed.Expr.Unfold v', code)
  | If0 (c, t, e) ->
      let c', acc' = r acc c in
      let t', acc' = r acc' t in
      let e', code = r acc' e in
      (Closed.Expr.If0 (c', t', e'), code)
  | Let ((n, t), e1, e2) ->
      let t' = cc_t t in
      let e1', acc' = r acc e1 in
      let e2', code = r acc' e2 in
      (Closed.Expr.Let ((n, t'), e1', e2'), code)
  | Cases (v, branches) ->
      let v', acc' = r acc v in
      let branches', code =
        List.fold_left
          ~f:(fun (branches, code) ((n, t), e) ->
            let t' = cc_t t in
            let e', new_code = r code e in
            (((n, t'), e') :: branches, new_code))
          ~init:([], acc') branches
      in
      (Closed.Expr.Cases (v', branches'), code)
  | Apply (f, ts, arg) ->
      let f', acc' = r acc f in
      let arg', code = r acc' arg in
      let ts' = List.map ~f:cc_t ts in
      let ft =
        match f' with
        | Var v -> List.Assoc.find_exn ~equal:equal_string gamma v |> cc_t
        | Pack (_, _, t) -> t
        | _ -> failwith "type error"
      in
      ( Closed.(
          Expr.Unpack
            ( "#cc-env",
              ("#env_and_fn", PreType.Prod [ PreType.Var "#cc-env"; ft ]),
              f',
              Expr.Let
                ( ("#env", PreType.Var "#cc-env"),
                  Expr.Project (0, Expr.Var "#env_and_fn"),
                  Expr.Let
                    ( ("#actual_fn", ft),
                      Expr.Project (1, Expr.Var "#env_and_fn"),
                      Expr.Apply (Expr.Var "#actual_fn", ts', arg') ) ) )),
        code )

let cc_imp (Source.Module.Import (n, t)) = Closed.Module.Import (n, cc_t t)

let cc_item user_fns gamma tagger acc item =
  let open Source in
  let open Module in
  match item with
  (* items will have no closed-over variables *)
  | Export
      ((n, t), Expr.Fun { foralls; arg = arg_name, arg_type; ret_type; body })
  | Private
      ((n, t), Expr.Fun { foralls; arg = arg_name, arg_type; ret_type; body })
    ->
      let body', extra = cc_e user_fns gamma tagger acc body in
      let packer =
        match item with
        | Export _ -> fun (a, b) -> Closed.Module.Export (a, b)
        | Private _ -> fun (a, b) -> Closed.Module.Private (a, b)
      in
      ( packer
          ( (n, cc_t t),
            Function
              {
                name = n;
                foralls;
                arg = (arg_name, cc_t arg_type);
                ret_type = cc_t ret_type;
                body = body';
              } ),
        extra )
  | _ -> failwith "items must be function"

let cc_module (Source.Module.Module (imps, items, body)) =
  let mk_private = function
    | Closed.Function.Function { name; foralls; arg = _, t; ret_type; _ } as f
      ->
        Closed.Module.Private
          ((name, Closed.PreType.Code { foralls; arg = t; ret = ret_type }), f)
  in
  let tagger = Tag.new_counter () in
  let initial_gamma =
    let open Source.Module in
    List.map ~f:(fun (Import (n, t)) -> (n, t)) imps
    @ List.map
        ~f:(function
          | Export ((n, t), _) | Private ((n, t), _) -> (n, t))
        items
  in
  let imps' =
    List.map
      ~f:(fun (Source.Module.Import (n, t)) -> Closed.Module.Import (n, cc_t t))
      imps
  in
  let items' =
    List.fold_left
      ~f:(fun acc item ->
        let item', extra = cc_item initial_gamma initial_gamma tagger [] item in
        let extra = List.map ~f:mk_private extra in
        acc @ extra @ [ item' ])
      ~init:[] items
  in
  let open Closed.Module in
  match body with
  | None -> Module (imps', items', None)
  | Some body ->
      let body', extra = cc_e initial_gamma initial_gamma tagger [] body in
      let extra = List.map ~f:mk_private extra in
      let items' = items' @ extra in
      Module (imps', items', Some body')
