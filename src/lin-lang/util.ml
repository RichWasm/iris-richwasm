open! Base

module type Monad = sig
  type 'a t

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Monad_ops (M : Monad) = struct
  open M

  let ( let* ) = bind
  let map (m : 'a t) (f : 'a -> 'b) : 'b t = bind m (fun x -> ret (f x))
  let ( let+ ) = map

  let apply (mf : ('a -> 'b) t) (mx : 'a t) : 'b t =
    let* f = mf in
    let* x = mx in
    ret (f x)

  let sequence (ms : 'a t list) : 'a list t =
    let rec go acc = function
      | [] -> ret (List.rev acc)
      | m :: ms ->
          let* x = m in
          go (x :: acc) ms
    in
    go [] ms

  let all = sequence

  let traverse ~(f : 'a -> 'b t) (xs : 'a list) : 'b list t =
    let rec go acc = function
      | [] -> ret (List.rev acc)
      | x :: xs ->
          let* y = f x in
          go (y :: acc) xs
    in
    go [] xs

  let mapM = traverse

  let foldM ~(f : 'acc -> 'a -> 'acc t) ~(init : 'acc) (xs : 'a list) : 'acc t =
    let rec go acc = function
      | [] -> ret acc
      | x :: xs ->
          let* acc' = f acc x in
          go acc' xs
    in
    go init xs

  let iterM (f : 'a -> unit t) (xs : 'a list) : unit t =
    foldM ~f:(fun () x -> f x) ~init:() xs

  let ( >=> ) f g x = bind (f x) g
  let ( >-> ) f g x = map (f x) g

  module Applicative = Applicative.Make (struct
    type 'a t = 'a M.t

    let return = ret
    let apply = apply
    let map = `Custom (fun m ~f -> map m f)
  end)
end

module type State = sig
  type t
end

module type Err = sig
  type t
end

module ResultM (E : Err) = struct
  module T = struct
    type 'a t = ('a, E.t) Result.t

    let ret (x : 'a) : 'a t = Ok x

    let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
      match m with
      | Error _ as er -> er
      | Ok x -> f x

    let fail err : 'a t = Error err
  end

  include T
  include Monad_ops (T)
end

module StateM (S : State) (E : Err) = struct
  module T = struct
    type 'a t = S.t -> ('a * S.t, E.t) Result.t

    let ret (x : 'a) : 'a t = fun e -> Ok (x, e)

    let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
     fun e ->
      match m e with
      | Error _ as er -> er
      | Ok (x, e') -> f x e'

    let fail err : 'a t = fun _ -> Error err
    let get : S.t t = fun s -> Ok (s, s)
    let put (s : S.t) : unit t = fun _ -> Ok ((), s)
    let modify (f : S.t -> S.t) : unit t = fun s -> Ok ((), f s)

    let lift_result (r : 'a ResultM(E).t) : 'a t =
     fun s ->
      match r with
      | Ok x -> Ok (x, s)
      | Error e -> Error e
  end

  include T
  include Monad_ops (T)
end
