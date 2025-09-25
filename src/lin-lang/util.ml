open! Base

module type State = sig
  type t
end

module type Err = sig
  type t
end

module StateM (S : State) (E : Err) = struct
  type 'a t = S.t -> ('a * S.t, E.t) Result.t

  let return (x : 'a) : 'a t = fun e -> Ok (x, e)

  let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
   fun e ->
    match m e with
    | Error _ as er -> er
    | Ok (x, e') -> f x e'

  let ( let* ) = bind

  let map m f =
   fun e ->
    match m e with
    | Error _ as er -> er
    | Ok (x, e') -> Ok (f x, e')

  let ( let+ ) = map
  let fail msg : 'a t = fun _ -> Error msg
  let get : S.t t = fun s -> Ok (s, s)
  let put (s : S.t) : unit t = fun _ -> Ok ((), s)
  let modify (f : S.t -> S.t) : unit t = fun s -> Ok ((), f s)

  let all (ms : 'a t list) : 'a list t =
    let rec go acc = function
      | [] -> return (List.rev acc)
      | m :: ms ->
          let* x = m in
          go (x :: acc) ms
    in
    go [] ms

  let mapM (f : 'a -> 'b t) (xs : 'a list) : 'b list t =
    let rec go acc = function
      | [] -> return (List.rev acc)
      | x :: xs ->
          let* y = f x in
          go (y :: acc) xs
    in
    go [] xs

  let foldM (f : 'acc -> 'a -> 'acc t) (init : 'acc) (xs : 'a list) : 'acc t =
    let rec go acc = function
      | [] -> return acc
      | x :: xs ->
          let* acc' = f acc x in
          go acc' xs
    in
    go init xs

  let iterM (f : 'a -> unit t) (xs : 'a list) : unit t =
    foldM (fun () x -> f x) () xs
end
