open! Core
open Syntax

let rec fv ?(bound = []) (e : Source.Expr.t) : Source.Variable.t list =
  let open Source.Expr in
  let open Source.Value in
  let rec free_v v =
    match v with
    | Int _ -> []
    | Var v ->
        if List.mem ~equal:equal_string bound v then
          []
        else
          [v]
    | Tuple vs -> List.concat_map ~f:free_v vs
    | Inj (_, v, _) -> free_v v
    | Fun {arg= n, _; body; _} -> fv ~bound:(n :: bound) body
  in
  match e with
  | Value v -> free_v v
  | Apply (f, _, arg) -> free_v f @ free_v arg
  | Project (_, v) -> free_v v
  | Op (_, l, r) -> free_v l @ free_v r
  | If0 (c, t, e) -> free_v c @ fv ~bound t @ fv ~bound e
  | New v -> free_v v
  | Deref v -> free_v v
  | Assign (r, v) -> free_v r @ free_v v
  | Fold (_, v) -> free_v v
  | Unfold v -> free_v v
  | Let ((n, _), e1, e2) -> fv ~bound e1 @ fv ~bound:(n :: bound) e2
  | Cases (v, branches) ->
      free_v v
      @ List.concat_map
          ~f:(fun ((n, _), e) -> fv ~bound:(n :: bound) e)
          branches
;;

let rec ftv ?(bound = []) (t : Source.Type.t) : Source.Variable.t list =
  let ftv_pt pt =
    let open Source.PreType in
    match pt with
    | Int -> []
    | Var v ->
        if List.mem ~equal:equal_string bound v then
          []
        else
          [v]
    | Prod ts -> List.concat_map ~f:(ftv ~bound) ts
    | Sum ts -> List.concat_map ~f:(ftv ~bound) ts
    | Ref t -> ftv ~bound t
    | Rec (v, t) -> ftv ~bound:(v :: bound) t
    | Fun {foralls; arg; ret} ->
        let bound = foralls @ bound in
        ftv ~bound arg @ ftv ~bound ret
  in
  ftv_pt t
;;

let rec ftv_e ?(bound = []) (e : Source.Expr.t) : Source.Variable.t list =
  let open Source.Expr in
  let open Source.Value in
  let ftv_v v =
    match v with
    | Inj (_, _, t) -> ftv ~bound t
    | Fun {foralls; arg= _, t; ret_type; body} ->
        (* TODO: do both of these have to be here? *)
        ftv (Fun {foralls; arg= t; ret= ret_type}) @ ftv_e ~bound:foralls body
    | Int _ | Var _ | Tuple _ -> []
  in
  match e with
  | Value v -> ftv_v v
  | Apply (f, ts, arg) ->
      ftv_v f @ List.concat_map ~f:(ftv ~bound) ts @ ftv_v arg
  | Project (_, v) -> ftv_v v
  | Op (_, l, r) -> ftv_v l @ ftv_v r
  | If0 (c, t, e) -> ftv_v c @ ftv_e t @ ftv_e e
  | Cases (v, branches) ->
      ftv_v v
      @ (branches |> List.unzip |> snd |> List.concat_map ~f:(ftv_e ~bound))
  | New v -> ftv_v v
  | Deref v -> ftv_v v
  | Assign (r, v) -> ftv_v r @ ftv_v v
  | Let (_, e1, e2) -> ftv_e ~bound e1 @ ftv_e ~bound e2
  | Fold (_, v) -> ftv_v v
  | Unfold v -> ftv_v v
;;

let rec cc_t t = cc_pt t

and cc_pt pt =
  match pt with
  | Source.PreType.Int -> Closed.PreType.Int
  | Source.PreType.Var v -> Closed.PreType.Var v
  | Source.PreType.Prod ts -> Closed.PreType.Prod (List.map ~f:cc_t ts)
  | Source.PreType.Sum ts -> Closed.PreType.Sum (List.map ~f:cc_t ts)
  | Source.PreType.Ref t -> Closed.PreType.Ref (cc_t t)
  | Source.PreType.Rec (v, t) -> Closed.PreType.Rec (v, cc_t t)
  | Source.PreType.Fun {foralls; arg; ret} ->
      Closed.(
        PreType.Exists
          ( "#cc-env",
            PreType.Code
              { foralls;
                arg= PreType.Prod [PreType.Var "#cc-env"; cc_t arg];
                ret= cc_t ret } ) )
;;

let rec cc_v gamma tagger acc v =
  match v with
  | Source.Value.Int i -> (Closed.Value.Int i, acc)
  | Source.Value.Var v -> (Closed.Value.Var v, acc)
  | Tuple vs ->
      let vs, code =
        List.fold_left
          ~f:(fun (vs, extra) v ->
            let converted, code = cc_v gamma tagger acc v in
            (converted :: vs, code @ extra) )
          ~init:([], acc) vs
      in
      (Closed.Value.Tuple vs, code)
  | Inj (i, v, t) ->
      let v, code = cc_v gamma tagger acc v in
      (Closed.Value.Inj (i, v, cc_t t), code)
  | Fun {foralls; arg= (n, t) as arg; ret_type; body} ->
      let gamma = arg :: gamma in
      let free_vars = fv (Value v) in
      let free_type_vars = ftv_e (Value v) in
      (* let arg_names, arg_types = List.unzip args in *)
      (* let arg_types = List.map ~f:cc_t arg_types in *)
      let closure_id = string_of_int (tagger ()) in
      let code_name = "closure#fn" ^ closure_id in
      let cced_body, code = cc_e gamma tagger acc body in
      let env_type =
        free_vars
        |> List.map ~f:(List.Assoc.find_exn ~equal:equal_string gamma)
        |> List.map ~f:cc_t
      in
      let env_prod = Closed.PreType.Prod env_type in
      let free_bindings = List.zip_exn free_vars env_type in
      Closed.
        ( Value.Pack
            ( env_prod,
              Value.Tuple
                [ Value.Tuple (List.map ~f:(fun v -> Value.Var v) free_vars);
                  Value.Var code_name ],
              PreType.Exists
                ( "#cc-env",
                  PreType.Code
                    { foralls= free_type_vars @ foralls;
                      arg= PreType.Prod [PreType.Var "#cc-env"; cc_t t];
                      ret= cc_t ret_type } ) ),
          ( code_name,
            Value.Fun
              { foralls= free_type_vars @ foralls;
                arg= ("#env_and_arg", PreType.Prod [env_prod; cc_t t]);
                ret_type= cc_t ret_type;
                body=
                  Expr.Let
                    ( ("#env", PreType.Var "#cc-env"),
                      Expr.Project (0, Value.Var "#env_and_arg"),
                      Expr.Let
                        ( (n, cc_t t),
                          Expr.Project (1, Value.Var "#env_and_arg"),
                          List.fold_right
                            ~f:(fun (idx, (name, ty)) acc ->
                              Expr.Let
                                ( (name, ty),
                                  Expr.Project (idx, Value.Var "#env"),
                                  acc ) )
                            ~init:cced_body
                            (List.zip_exn
                               (List.range 0 (List.length free_bindings))
                               free_bindings ) ) ) } )
          :: code )

and cc_e gamma tagger acc e =
  let open Source.Expr in
  match e with
  | Value v ->
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.Value v', code)
  | Project (i, v) ->
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.Project (i, v'), code)
  | Op (o, l, r) ->
      let l', acc' = cc_v gamma tagger acc l in
      let r', code = cc_v gamma tagger acc' r in
      (Closed.Expr.Op (o, l', r'), code)
  | New v ->
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.New v', code)
  | Deref v ->
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.Deref v', code)
  | Assign (r, v) ->
      let r', acc' = cc_v gamma tagger acc r in
      let v', code = cc_v gamma tagger acc' v in
      (Closed.Expr.Assign (r', v'), code)
  | Fold (t, v) ->
      let t' = cc_t t in
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.Fold (t', v'), code)
  | Unfold v ->
      let v', code = cc_v gamma tagger acc v in
      (Closed.Expr.Unfold v', code)
  | If0 (c, t, e) ->
      let c', acc' = cc_v gamma tagger acc c in
      let t', acc' = cc_e gamma tagger acc' t in
      let e', code = cc_e gamma tagger acc' e in
      (Closed.Expr.If0 (c', t', e'), code)
  | Let ((n, t), e1, e2) ->
      let t' = cc_t t in
      let e1', acc' = cc_e gamma tagger acc e1 in
      let e2', code = cc_e gamma tagger acc' e2 in
      (Closed.Expr.Let ((n, t'), e1', e2'), code)
  | Cases (v, branches) ->
      let v', acc' = cc_v gamma tagger acc v in
      let branches', code =
        List.fold_left
          ~f:(fun (branches, code) ((n, t), e) ->
            let t' = cc_t t in
            let e', new_code = cc_e gamma tagger code e in
            (((n, t'), e') :: branches, new_code) )
          ~init:([], acc') branches
      in
      (Closed.Expr.Cases (v', branches'), code)
  | Apply (f, ts, arg) ->
      let f', acc' = cc_v gamma tagger acc f in
      let arg', code = cc_v gamma tagger acc' arg in
      let ts' = List.map ~f:cc_t ts in
      let ft =
        match f' with
        | Closed.Value.Var v ->
            List.Assoc.find_exn ~equal:equal_string gamma v |> cc_t
        | Closed.Value.Pack (_, _, t) -> t
        | _ -> failwith "type error"
      in
      ( Closed.(
          Expr.Unpack
            ( "#cc-env",
              ("#env_and_fn", PreType.Prod [PreType.Var "#cc-env"; ft]),
              f',
              Expr.Let
                ( ("#env", PreType.Var "#cc-env"),
                  Expr.Project (0, Value.Var "#env_and_fn"),
                  Expr.Let
                    ( ("#actual_fn", ft),
                      Expr.Project (1, Value.Var "#env_and_fn"),
                      Expr.Apply (Value.Var "#actual_fn", ts', arg') ) ) ) ),
        code )
;;

let cc_imp (Source.Module.Import (n, t)) = Closed.Module.Import (n, cc_t t)

let cc_item gamma tagger acc =
  let open Source.Module in
  function
  | Export ((n, t), e) ->
      ( (fun ((n, t), e) -> Closed.Module.Export ((n, t), e)),
        (n, cc_t t),
        cc_e gamma tagger acc e )
  | Private ((n, t), e) ->
      ( (fun ((n, t), e) -> Closed.Module.Private ((n, t), e)),
        (n, cc_t t),
        cc_e gamma tagger acc e )
;;
