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

let pp_pad ff ?(fill = ' ') ~len is_right =
  let margin = pp_get_margin ff () in
  let pad = pad ~fill ((margin - 2 - len) / 2) in
  fprintf ff "%s" pad;
  if is_right && len % 2 = 1 then fprintf ff "%c" fill

let kasprintf_cust
    ~cust
    (type a)
    (type b)
    (k : string -> a)
    (f : (b, Stdlib.Format.formatter, unit, a) format4) : b =
  let buf = Buffer.create 512 in
  let fmt = formatter_of_buffer buf in
  cust fmt;
  kfprintf
    (fun fmt ->
      pp_print_flush fmt ();
      buf |> Buffer.contents |> k)
    fmt f
