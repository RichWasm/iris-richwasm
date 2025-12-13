open! Base
open! Stdlib.Format

let flatten (lst : 'a list list) : 'a list =
  let rec go acc = function
    | [] -> List.rev acc
    | m :: ms -> go (List.rev_append m acc) ms
  in
  go [] lst

include Richwasm_common.Monads
include Richwasm_common.Util

let pp_list pp sep xs =
  List.iteri
    ~f:(fun i x ->
      if i > 0 then sep ();
      pp x)
    xs

let pp_sep pp ff ~(sep : string) ts =
  fprintf ff "@[(";
  pp_list (fun x -> fprintf ff "%a" pp x) (fun () -> fprintf ff "@ %s@ " sep) ts;
  fprintf ff ")@]"
