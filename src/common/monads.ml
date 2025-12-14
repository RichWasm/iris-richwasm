open! Base

let ( << ) g f x = g (f x)
let ( >> ) f g x = g (f x)

module Monad = struct
  module type Basic = sig
    type 'a t

    val ret : 'a -> 'a t
    val bind : 'a t -> ('a -> 'b t) -> 'b t
  end

  module Make (M : Basic) = struct
    include M

    let ( let* ) = bind
    let ( >>= ) = bind
    let map (m : 'a t) (f : 'a -> 'b) : 'b t = bind m (fun x -> ret (f x))
    let ( let+ ) = map
    let ( >>| ) = map

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

    let traverse (lst : 'a list) ~(f : 'a -> 'b t) : 'b list t =
      let rec go acc = function
        | [] -> ret (List.rev acc)
        | x :: xs ->
            let* y = f x in
            go (y :: acc) xs
      in
      go [] lst

    let mapM = traverse

    let flat_mapM lst ~(f : 'a -> 'b list t) : 'b list t =
      let rec go acc = function
        | [] -> ret (List.rev acc)
        | x :: xs ->
            let* y = f x in
            go (List.rev_append y acc) xs
      in
      go [] lst

    let traversei (lst : 'a list) ~(f : int -> 'a -> 'b t) : 'b list t =
      let rec go i acc = function
        | [] -> ret acc
        | x :: xs ->
            let* y = f i x in
            go (i + 1) (y :: acc) xs
      in
      let+ res = go 0 [] lst in
      List.rev res

    let mapiM = traversei

    let foldM (lst : 'a list) ~(f : 'b -> 'a -> 'b t) ~(init : 'b) : 'b t =
      let rec go acc = function
        | [] -> ret acc
        | x :: xs ->
            let* acc' = f acc x in
            go acc' xs
      in
      go init lst

    let foldiM (lst : 'a list) ~(f : int -> 'b -> 'a -> 'b t) ~(init : 'b) :
        'b t =
      let rec go i acc = function
        | [] -> ret acc
        | x :: xs ->
            let* acc' = f i acc x in
            go (i + 1) acc' xs
      in
      go 0 init lst

    let iterM ~(f : 'a -> unit t) (xs : 'a list) : unit t =
      foldM ~f:(fun () x -> f x) ~init:() xs

    let iteriM ~(f : int -> 'a -> unit t) (xs : 'a list) : unit t =
      foldiM ~f:(fun i () x -> f i x) ~init:() xs

    let omap ~(f : 'a -> 'b t) (x : 'a option) : 'b option t =
      match x with
      | None -> ret None
      | Some x ->
          let+ x' = f x in
          Some x'

    let ( >=> ) f g x = bind (f x) g
    let ( >-> ) f g x = map (f x) g

    module Applicative = Applicative.Make (struct
      type 'a t = 'a M.t

      let return = ret
      let apply = apply
      let map = `Custom (fun m ~f -> map m f)
    end)
  end
end

module Monad_with_fail = struct
  module type Basic = sig
    include Monad.Basic

    type error

    val fail : error -> 'a t
    val map_error : 'a t -> f:(error -> error) -> 'a t
  end

  module Make (M : Basic) = struct
    open M

    let fail_if cond err : 'a t = if cond then fail err else ret ()
    let fail_ifn cond err : 'a t = if cond then ret () else fail err

    let lift_option err : 'a Option.t -> 'a t = function
      | Some x -> ret x
      | None -> fail err
  end
end

module Monad_with_fail_and_log = struct
  module type Basic = sig
    include Monad_with_fail.Basic

    type log_item

    val tell : log_item -> unit t
  end

  module Make (M : Basic) = struct
    include M
    include Monad.Make (M)
    include Monad_with_fail.Make (M)

    let tap (item_of : 'a -> log_item) (m : 'a t) : 'a t =
      let* x = m in
      let* () = tell (item_of x) in
      ret x
  end
end

module ResultM (E : T) = struct
  module T = struct
    type error = E.t
    type 'a t = ('a, error) Result.t

    let ret (x : 'a) : 'a t = Ok x

    let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
      match m with
      | Error _ as er -> er
      | Ok x -> f x

    let fail err : 'a t = Error err
    let map_error = Result.map_error
  end

  include T
  include Monad.Make (T)
  include Monad_with_fail.Make (T)
end

module LogResultM (E : T) (L : T) = struct
  module T = struct
    type error = E.t
    type log_item = L.t
    type 'a t = log_item list -> ('a, error) Result.t * log_item list

    let ret x : 'a t = fun log -> (Ok x, log)
    let fail e : 'a t = fun log -> (Error e, log)

    let bind m f =
     fun log0 ->
      match m log0 with
      | Error e, log1 -> (Error e, log1)
      | Ok x, log1 -> f x log1

    let tell item = fun log -> (Ok (), log @ [ item ])

    let map_error (m : 'a t) ~(f : error -> error) : 'a t =
     fun log0 ->
      match m log0 with
      | Ok x, log1 -> (Ok x, log1)
      | Error e, log1 -> (Error (f e), log1)

    let lift_result (r : ('a, error) Result.t) : 'a t =
      match r with
      | Ok x -> ret x
      | Error e -> fail e

    let run (m : 'a t) : ('a, error) Result.t * log_item list = m []
  end

  let map_error_into
      (f : 'e1 -> 'e2)
      (m : 'l list -> ('a, 'e1) Result.t * 'l list) :
      'l list -> ('a, 'e2) Result.t * 'l list =
   fun log0 ->
    match m log0 with
    | Ok x, log1 -> (Ok x, log1)
    | Error e, log1 -> (Error (f e), log1)

  include T
  include Monad_with_fail_and_log.Make (T)
end

module StateM (S : T) (E : T) = struct
  module T = struct
    type error = E.t
    type 'a t = S.t -> ('a * S.t, error) Result.t

    let ret (x : 'a) : 'a t = fun e -> Ok (x, e)

    let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
     fun e ->
      match m e with
      | Error _ as er -> er
      | Ok (x, e') -> f x e'

    let fail err : 'a t = fun _ -> Error err

    let map_error (m : 'a t) ~f : 'a t =
     fun s ->
      match m s with
      | Ok _ as ok -> ok
      | Error e -> Error (f e)

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
  include Monad.Make (T)
  include Monad_with_fail.Make (T)
end
