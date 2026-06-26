open! Base
open Syntax
open Richwasm_common.Monads

module Err = struct
  type t =
    | UnboundIdent of string
    | UserFnNotFunction of string * Source.PreType.t
    | ApplyBadShape of Closed.Expr.t
    | ApplyVarNotInGamma of string
    | ItemNotFunction
    | FreeVarNotInGamma of string
    | FreeVarsLengthMismatch of int * int
  [@@deriving sexp_of, variants]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = ResultM (Err)

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
  | Tuple vs | UTuple vs -> List.concat_map ~f:fe vs
  | Inj (_, v, _) | UInj (_, v, _) -> fe v
  | Fun { arg = n, _; body; _ } -> fv ~bound:(n :: bound) body
  | Apply (f, _, arg) -> fe f @ fe arg
  | Project (_, v) -> fe v
  | Op (_, l, r) -> fe l @ fe r
  | If0 (c, t, e) -> fe c @ fe t @ fe e
  | New v -> fe v
  | Deref v -> fe v
  | Assign (r, v) | Swap (r, v) -> fe r @ fe v
  | Fold (_, v) -> fe v
  | Unfold v -> fe v
  | Let ((n, _), e1, e2) -> fe e1 @ fv ~bound:(n :: bound) e2
  | Split (bs, e1, e2) -> fe e1 @ fv ~bound:(List.map ~f:fst bs @ bound) e2
  | Cases (v, branches) | UCase (v, branches) ->
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
    | Prod ts | UProd ts | USum ts | Sum ts ->
        List.concat_map ~f:(ftv ~bound) ts
    | Ref t | LinRef t -> ftv ~bound t
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
  | Inj (_, _, t) | UInj (_, _, t) -> ftv ~bound t
  | Fun { foralls; arg = _, t; ret_type; body } ->
      (* TODO: do both of these have to be here? *)
      ftv (Fun { foralls; arg = t; ret = ret_type }) @ ftv_e ~bound:foralls body
  | Int _ | Var _ -> []
  | Tuple vs | UTuple vs -> List.concat_map ~f:r vs
  | Apply (f, ts, arg) -> r f @ List.concat_map ~f:(ftv ~bound) ts @ r arg
  | Project (_, v) -> r v
  | Op (_, left, right) -> r left @ r right
  | If0 (c, t, e) -> r c @ r t @ r e
  | Cases (v, branches) | UCase (v, branches) ->
      r v @ (branches |> List.unzip |> snd |> List.concat_map ~f:(ftv_e ~bound))
  | New v -> r v
  | Deref v -> r v
  | Assign (re, v) | Swap (re, v) -> r re @ r v
  | Let (_, e1, e2) -> r e1 @ r e2
  | Split (bs, e1, e2) ->
      List.concat_map ~f:(fun (_, t) -> ftv ~bound t) bs @ r e1 @ r e2
  | Fold (_, v) -> r v
  | Unfold v -> r v

let rec cc_t ?(pack = true) t = cc_pt ~pack t

and cc_pt ?(pack = true) (pt : Source.PreType.t) =
  let open Closed.PreType in
  (* the ~pack argument is basically a hack, and doesn't wrap function types
     in an existential for imports. but any function types referenced inside
     that function _should_ get treated normally. *)
  let cc_t = cc_t ~pack:true in
  match pt with
  | Int -> Int
  | Var v -> Var v
  | Prod ts -> Prod (List.map ~f:cc_t ts)
  | UProd ts -> UProd (List.map ~f:cc_t ts)
  | USum ts -> USum (List.map ~f:cc_t ts)
  | Sum ts -> Sum (List.map ~f:cc_t ts)
  | Ref t -> Ref (cc_t t)
  | LinRef t -> LinRef (cc_t t)
  | Rec (v, t) -> Rec (v, cc_t t)
  | Fun { foralls; arg; ret } ->
      if pack then
        Exists
          ( "#cc-env",
            Prod
              [
                Var "#cc-env";
                Code
                  {
                    foralls;
                    args = [ Var "#cc-env"; cc_t arg ];
                    ret = cc_t ret;
                  };
              ] )
      else
        Code { foralls; args = [ Prod []; cc_t arg ]; ret = cc_t ret }

let rec cc_e
    (user_fns : (string * Source.PreType.t) list)
    (gamma : (string * Source.PreType.t) list)
    tagger
    acc
    (e : Source.Expr.t) : (Closed.Expr.t * Closed.Function.t list) Res.t =
  let open Res in
  let open Closed.PreType in
  let open Closed.Function in
  let open Closed.Expr in
  let r = cc_e user_fns gamma tagger in
  let r_list acc vs =
    let* vs_rev, code =
      foldM
        ~f:(fun (vs, extra) v ->
          let* converted, code = r extra v in
          ret (converted :: vs, code))
        ~init:([], acc) vs
    in
    ret (List.rev vs_rev, code)
  in
  match e with
  | Int i -> ret (Int i, acc)
  | Var v ->
      if List.Assoc.mem ~equal:equal_string gamma v then
        ret (Var v, acc)
      else (
        match
          List.Assoc.find ~equal:equal_string user_fns v
        with
        | Some (Fun { foralls; arg; ret = ret_t } as t) ->
            ret
              ( Pack
                  ( Prod [],
                    Tuple
                      [
                        Tuple [];
                        Coderef
                          ( Code
                              {
                                foralls;
                                args = [ Prod []; cc_t arg ];
                                ret = cc_t ret_t;
                              },
                            v );
                      ],
                    cc_t t ),
                acc )
        | Some t -> fail (UserFnNotFunction (v, t))
        | None -> fail (UnboundIdent v))
  | Tuple vs ->
      let* vs', code = r_list acc vs in
      ret (Tuple vs', code)
  | UTuple vs ->
      let* vs', code = r_list acc vs in
      ret (UTuple vs', code)
  | Inj (i, v, t) ->
      let* v, code = r acc v in
      ret (Inj (i, v, cc_t t), code)
  | UInj (i, v, t) ->
      let* v, code = r acc v in
      ret (UInj (i, v, cc_t t), code)
  | Fun { foralls; arg = (n, t) as arg; ret_type; body } ->
      let gamma = arg :: gamma in
      let free_vars = fv ~bound:[ n ] body in
      (* NOTE: exclude this fn's own type params (bound by [foralls]); counting them doubles the closure's quantifiers, leaving a stray forall at calls. *)
      let free_type_vars = ftv_e ~bound:foralls body in
      let closure_id = Int.to_string (tagger ()) in
      let code_name = "closure#fn" ^ closure_id in
      let* cced_body, code = cc_e user_fns gamma tagger acc body in
      let* env_type =
        mapM free_vars ~f:(fun v ->
            match List.Assoc.find ~equal:equal_string gamma v with
            | Some t -> ret (cc_t t)
            | None -> fail (FreeVarNotInGamma v))
      in
      let env_prod = Prod env_type in
      let* free_bindings =
        match List.zip free_vars env_type with
        | Ok bs -> ret bs
        | Unequal_lengths ->
            fail
              (FreeVarsLengthMismatch
                 (List.length free_vars, List.length env_type))
      in
      let function_type =
        Code
          {
            foralls = free_type_vars @ foralls;
            args = [ env_prod; cc_t t ];
            ret = cc_t ret_type;
          }
      in
      ret
        ( Pack
            ( env_prod,
              Tuple
                [
                  Tuple (List.map ~f:(fun v -> Var v) free_vars);
                  Coderef (function_type, code_name);
                ],
              Exists
                ( "#cc-env",
                  Prod
                    [
                      Var "#cc-env";
                      Code
                        {
                          foralls = free_type_vars @ foralls;
                          args = [ Var "#cc-env"; cc_t t ];
                          ret = cc_t ret_type;
                        };
                    ] ) ),
          Function
            {
              name = code_name;
              foralls = free_type_vars @ foralls;
              args = [ ("#env", env_prod); (n, cc_t t) ];
              ret_type = cc_t ret_type;
              body =
                List.fold_right
                  ~f:(fun (idx, (name, ty)) acc ->
                    Let ((name, ty), Project (idx, Var "#env"), acc))
                  ~init:cced_body
                  (List.zip_exn
                     (List.range 0 (List.length free_bindings))
                     free_bindings);
            }
          :: code )
  | Project (i, v) ->
      let* v', code = r acc v in
      ret (Project (i, v'), code)
  | Op (o, left, right) ->
      let* l', acc' = r acc left in
      let* r', code = r acc' right in
      ret (Op (o, l', r'), code)
  | New v ->
      let* v', code = r acc v in
      ret (New v', code)
  | Deref v ->
      let* v', code = r acc v in
      ret (Deref v', code)
  | Assign (re, v) ->
      let* r', acc' = r acc re in
      let* v', code = r acc' v in
      ret (Assign (r', v'), code)
  | Swap (re, v) ->
      let* r', acc' = r acc re in
      let* v', code = r acc' v in
      ret (Swap (r', v'), code)
  | Fold (t, v) ->
      let t' = cc_t t in
      let* v', code = r acc v in
      ret (Fold (t', v'), code)
  | Unfold v ->
      let* v', code = r acc v in
      ret (Unfold v', code)
  | If0 (c, t, e) ->
      let* c', acc' = r acc c in
      let* t', acc' = r acc' t in
      let* e', code = r acc' e in
      ret (If0 (c', t', e'), code)
  | Let ((n, t), e1, e2) ->
      let t' = cc_t t in
      let* e1', acc' = r acc e1 in
      let* e2', code = cc_e user_fns ((n, t) :: gamma) tagger acc' e2 in
      ret (Let ((n, t'), e1', e2'), code)
  | Split (bs, e1, e2) ->
      let bs' = List.map ~f:(fun (n, t) -> (n, cc_t t)) bs in
      let* e1', acc' = r acc e1 in
      let* e2', code = cc_e user_fns (bs @ gamma) tagger acc' e2 in
      ret (Split (bs', e1', e2'), code)
  | Cases (v, branches) ->
      let* v', acc' = r acc v in
      let* branches_rev, code =
        foldM
          ~f:(fun (branches, code) ((n, t), e) ->
            let t' = cc_t t in
            let* e', new_code = cc_e user_fns ((n, t) :: gamma) tagger code e in
            ret (((n, t'), e') :: branches, new_code))
          ~init:([], acc') branches
      in
      ret (Cases (v', List.rev branches_rev), code)
  | UCase (v, branches) ->
      let* v', acc' = r acc v in
      let* branches_rev, code =
        foldM
          ~f:(fun (branches, code) ((n, t), e) ->
            let t' = cc_t t in
            let* e', new_code = cc_e user_fns ((n, t) :: gamma) tagger code e in
            ret (((n, t'), e') :: branches, new_code))
          ~init:([], acc') branches
      in
      ret (UCase (v', List.rev branches_rev), code)
  | Apply (f, ts, arg) ->
      let* f', acc' = r acc f in
      let* arg', code = r acc' arg in
      let ts' = List.map ~f:cc_t ts in
      let* ft =
        match f' with
        | Var v ->
            (match List.Assoc.find ~equal:equal_string gamma v with
            | Some t -> ret (cc_t t)
            | None -> fail (ApplyVarNotInGamma v))
        | Pack (_, _, t) -> ret t
        | _ -> fail (ApplyBadShape f')
      in
      ret
        ( Unpack
            ( "#cc-env",
              ("#env_and_fn", Prod [ Var "#cc-env"; ft ]),
              f',
              Let
                ( ("#env", Var "#cc-env"),
                  Project (0, Var "#env_and_fn"),
                  Let
                    ( ("#actual_fn", ft),
                      Project (1, Var "#env_and_fn"),
                      Apply (Var "#actual_fn", ts', [ Var "#env"; arg' ]) ) ) ),
          code )

let cc_imp (Source.Module.Import (n, t)) = Closed.Module.Import (n, cc_t t)

let cc_item user_fns gamma tagger acc item :
    (Closed.Module.item * Closed.Function.t list) Res.t =
  let open Source in
  let open Module in
  let open PreType in
  let open Res in
  let unit_type = PreType.Prod [] in
  match item with
  | Export ((n, t), Fun { foralls; arg = arg_name, arg_type; ret_type; body })
  | Private ((n, t), Fun { foralls; arg = arg_name, arg_type; ret_type; body })
    ->
      (* top-level functions have a unit environment, passed as the first
         argument for uniformity with closures *)
      let* body', extra =
        cc_e user_fns
          (("#env", unit_type) :: (arg_name, arg_type) :: gamma)
          tagger acc body
      in
      let packer =
        let open Closed.Module in
        match item with
        | Export _ -> fun (a, b) -> Export (a, b)
        | Private _ -> fun (a, b) -> Private (a, b)
      in
      ret
        ( packer
            ( (n, cc_t t),
              Function
                {
                  name = n;
                  foralls;
                  args = [ ("#env", cc_t unit_type); (arg_name, cc_t arg_type) ];
                  ret_type = cc_t ret_type;
                  body = body';
                } ),
          extra )
  | _ -> fail ItemNotFunction

let cc_module (Source.Module.Module (imps, items, body)) : Closed.Module.t Res.t
    =
  let open Res in
  let mk_private : Closed.Function.t -> Closed.Module.item = function
    | Function { name; foralls; args; ret_type; _ } as f ->
        Private
          ( (name, Code { foralls; args = List.map ~f:snd args; ret = ret_type }),
            f )
  in
  let tagger = Tag.new_counter () in
  let user_fns =
    let open Source.Module in
    List.map ~f:(fun (Import (n, t)) -> (n, t)) imps
    @ List.map
        ~f:(function
          | Export ((n, t), _) | Private ((n, t), _) -> (n, t))
        items
  in
  let imps' =
    List.map
      ~f:(fun (Source.Module.Import (n, t)) ->
        (* imports are of actual function type, not packed existential. they're
           added in [user_fns] so they get packed on use. *)
        Closed.Module.Import (n, cc_t ~pack:false t))
      imps
  in
  let* items' =
    foldM
      ~f:(fun acc item ->
        let* item', extra = cc_item user_fns [] tagger [] item in
        let extra = List.map ~f:mk_private extra in
        ret (acc @ extra @ [ item' ]))
      ~init:[] items
  in
  let open Closed.Module in
  match body with
  | None -> ret (Module (imps', items', None))
  | Some body ->
      let* body', extra = cc_e user_fns [] tagger [] body in
      let extra = List.map ~f:mk_private extra in
      let items' = items' @ extra in
      ret (Module (imps', items', Some body'))
