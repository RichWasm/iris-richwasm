open! Base
open Stdlib.Format

let pp_print_list_pre ?(pp_sep = pp_print_cut) pp_v ppf v =
  List.iter
    ~f:(fun x ->
      pp_sep ppf ();
      pp_v ppf x)
    v

let pp_print_list_post ?(pp_sep = pp_print_cut) pp_v ppf v =
  List.iter
    ~f:(fun x ->
      pp_v ppf x;
      pp_sep ppf ())
    v

let pp_print_list_space pp_v ppf v =
  pp_print_list ~pp_sep:pp_print_space pp_v ppf v

let pp_print_list_pre_space pp_v ppf v =
  pp_print_list_pre ~pp_sep:pp_print_space pp_v ppf v

let pp_print_list_post_space pp_v ppf v =
  pp_print_list_post ~pp_sep:pp_print_space pp_v ppf v

let pp_print_hard_space ff () = fprintf ff " "
let pp_print_nothing ff () = fprintf ff ""

let pad ?(fill = ' ') n =
  if n <= 0 then
    ""
  else
    String.make n fill
