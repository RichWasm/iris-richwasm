open! Base
open Sexplib
open Result

module Path = struct
  type seg =
    | Tag of string
    | Field of string
    | Idx of int
    | Choice of string
    | Alt of string
    | Commit
  [@@deriving sexp]

  type t = seg list [@@deriving sexp]

  let empty : t = []
  let length : Path.t -> int = List.length

  let add ?(commit = true) ~(tag : string) ~(field : string) (ctx : t) =
    if commit then
      Field field :: Commit :: Tag tag :: ctx
    else
      Field field :: Tag tag :: ctx

  let choose (p : t) (name : string) : t = Choice name :: p
  let alt (p : t) (alt : string) : t = Alt alt :: p
  let commit (p : t) : t = Commit :: p

  let score (p : t) : int * int =
    let commits, depth =
      List.fold_left
        ~f:(fun (c, d) -> function
          | Commit -> (c + 1, d + 1)
          | _ -> (c, d + 1))
        ~init:(0, 0) p
    in
    (commits, depth)
end

module type ERR = sig
  type t [@@deriving sexp_of]

  val pp : Stdlib.Format.formatter -> t -> unit
  val path_of : t -> Path.t
  val prefer : t -> t -> t
  val expected_expr : Path.t -> Sexp.t -> t
end

module SexpParser (Err : ERR) = struct
  module Res = Monads.ResultM (Err)

  let choice
      (type a)
      (name : string)
      (p : Path.t)
      (sexp : Sexp.t)
      (alts : ((Path.t -> Sexp.t -> a Res.t) * string) list) : a Res.t =
    let p_choice = Path.choose p name in
    let rec go best = function
      | [] ->
          (match best with
          | None -> Error (Err.expected_expr p_choice sexp)
          | Some e -> Error e)
      | (f, alt_name) :: fs ->
          let p_alt = Path.alt p_choice alt_name in
          (match f p_alt sexp with
          | Ok x -> Ok x
          | Error e ->
              let best' =
                Some
                  (match best with
                  | None -> e
                  | Some b -> Err.prefer b e)
              in
              go best' fs)
    in
    go None alts
end
