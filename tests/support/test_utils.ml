open! Base
open! Stdlib.Format

let or_fail (p : 'b -> string) : ('a, 'b) Result.t -> 'a = function
  | Ok x -> x
  | Error err -> failwith (p err)

let or_fail_pp (pp : formatter -> 'b -> unit) : ('a, 'b) Result.t -> 'a =
  or_fail (asprintf "%a" pp)
