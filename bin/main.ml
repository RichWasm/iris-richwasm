open! Printf
open! Sexplib
open Richwasm_lin_lang.Syntax

let () =
  let modu : Module.t =
    Module
      ([Import (Lolipop (Int, (Prod (Int, Int))), "dup-int")],
       [],
       Some(App (Lam (("x", Int), Int, Val (Var "x")), Int 10)))
  in
  let sexp = Module.sexp_of_t modu in
  (*  printf "%s\n" (Sexp.show sexp); *)
  let str = Sexp.to_string_hum sexp in
  printf "%s\n" str ;
  printf "%s\n" (Module.string_of modu)
