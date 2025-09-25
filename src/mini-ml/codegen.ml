open! Base
open Syntax
open Richwasm_common

let kind =
  (* the kind of all mini-ml types: [VALTYPE ptr ExCopy ExDrop] *)
  RichWasm.Kind.VALTYPE
    ( RichWasm.Representation.PrimR RichWasm.PrimitiveRep.PtrR,
      RichWasm.Copyability.ExCopy,
      RichWasm.Dropability.ExDrop )
;;

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
;;

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
      | Code { foralls; ret; _ } ->
          List.fold_right2_exn ~init:ret
            ~f:(fun var arg acc -> type_subst var arg acc)
            foralls ts
      | _ -> failwith "application should be on a function")
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
;;

let rec compile_value gamma localctx v =
  let open Closed.Value in
  match v with
  | Int i ->
      [
        RichWasm.Instruction.INumConst
          ( RichWasm.Internal.Types.InstrT
              ( [],
                [
                  RichWasm.Internal.Types.NumT
                    (kind, RichWasm.NumType.IntT RichWasm.Int.Type.I32T);
                ] ),
            Z.of_int i );
      ]
  | Tuple vs ->
      List.concat_map ~f:(compile_value gamma localctx) vs
      @ [ RichWasm.Instruction.IGroup (failwith "") ]
  | _ -> failwith ""
;;
