open! Base
open! Stdlib.Format

let flatten (lst : 'a list list) : 'a list =
  let rec go acc = function
    | [] -> List.rev acc
    | m :: ms -> go (List.rev_append m acc) ms
  in
  go [] lst

include Richwasm_common.Monads

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

let pp_print_list_pre ?(pp_sep = pp_print_cut) pp_v ppf v =
  List.iter
    ~f:(fun x ->
      pp_sep ppf ();
      pp_v ppf x)
    v

let pp_print_hard_space ff () = fprintf ff " "
let pp_print_nothing ff () = fprintf ff ""
