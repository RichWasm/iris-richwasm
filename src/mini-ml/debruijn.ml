open Syntax

let some_if c v = if c then Some v else None

module Env = struct
  type t = (string * [ `Var | `Global | `Fun ]) list

  let empty = []
  let add_var s t = (s, `Var) :: t
  let add_global s t = (s, `Global) :: t
  let add_fun s t = (s, `Fun) :: t

  let find s t =
    let (found, (`Var _, `Global global_count, `Fun fun_count)) =
      List.fold_left
        (fun (found, (`Var var_count, `Global global_count, `Fun fun_count)) (e, kind) ->
          let kind_result, new_counts =
            let eq = String.equal e s in
            match kind with
            | `Var ->
              (
                some_if eq (`Var var_count),
                (`Var (var_count + 1), `Global global_count, `Fun fun_count)
              )
            | `Global ->
              (
                some_if eq (`Global global_count),
                (`Var var_count, `Global (global_count + 1), `Fun fun_count)
              )
            | `Fun ->
              (
                some_if eq (`Fun fun_count),
                (`Var var_count, `Global global_count, `Fun (fun_count + 1))
              )
          in
          match found with
          | Some _ -> (found, new_counts)
          | None -> (kind_result, new_counts))
        (None, (`Var 0, `Global 0, `Fun 0))
        t
      in
      Option.map (function
          | `Var n -> (`Var, n)
          | `Global n -> (`Global, global_count - (n + 1))
          | `Fun n -> (`Fun, fun_count - (n + 1)))
        found
  ;;
end

type unbound = Unbound of string

let rec debruijn_t (delta : Env.t) (t : Source.Type.t) : (Debruijned.Type.t, unbound) result =
  match t with
  | Int -> Ok Debruijned.Type.Int
  | Prod ts ->
    let folded = List.fold_left
      (fun acc t ->
        match acc with
        | Ok acc ->
          (match debruijn_t delta t with
          | Ok t -> Ok (t :: acc)
          | Error e -> Error e)
         | Error e -> Error e)
        (Ok [])
        ts
    in
    Result.map (fun ts -> Debruijned.Type.Prod ts) folded
  | _ -> Ok Int
  (* match t with
  | Int -> return Int
  | Var v ->
    (match Debruijn_env.find v delta with
     | Some (`Var, i) -> return (Var i)
     | _ -> Or_error.error_s [%message "Unbound type variable" (v : string)])
  | Fun { foralls; args; ret } ->
    let delta = List.fold_left
      (Fun.flip Debruijn_env.add_var)
      delta
      foralls
    in
    let%bind args =
      List.map ~f:(debruijn_t ~delta) args |> Or_error.all
    in
    let%bind ret = debruijn_t ~delta ret in
    return (Fun { foralls = List.length foralls; args; ret })
  | Ref t ->
    let%bind t = h t in
    return (Ref t)
  | Prod ts ->
    let%bind ts = List.map ~f:h ts |> Or_error.all in
    return (Prod ts)
  | Sum ts ->
    let%bind ts = List.map ~f:h ts |> Or_error.all in
    return (Sum ts)
  | Rec (v, t) ->
    let%bind t = debruijn_t ~delta:(Debruijn_env.add_var v delta) t in
    return (Rec t) *)
;;
