open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Syntax

let simple_app_lambda : Module.t =
  Parse.from_string_exn
    {|
      (app
        (lam (x : int) : int .
          x)
        10)
    |}

let add_one_program : Module.t =
  Parse.from_string_exn
    {|
      (export fun add-one (x : int) : int .
        (x + 1))
      (app add-one 42)
    |}

let add_tup_ref : Module.t =
  Parse.from_string_exn
    {|
      (let (r : (ref int)) = (new 2) in
      (split (x1 : int) (x2 : (ref int)) = (tup 1 r) in
      (let (x2' : int) = (free x2) in
        (x1 + x2'))))
    |}

let print_10 : Module.t =
  Parse.from_string_exn
    {|
      (import (int -o ()) as print)

      (print 10)
    |}

let factorial_program : Module.t =
  Parse.from_string_exn
    {|
      (export fun factorial (n : int) : int .
        (if0 n
          then 1
          else
            (let (n-sub1 : int) = (n - 1) in
            (let (rec-res : int) = (app factorial n-sub1) in
            (n * rec-res)))))
      (app factorial 5)
    |}

let safe_div =
  Parse.from_string_exn
    {|
      (fun safe_div (p : (int ⊗ int)) : (int ⊕ ()) .
        (split (x : int) (y : int) = p in
        (if0 y then
          (inj 1 () : (int ⊕ ()))
        else
          (let (q : int) = (x ÷ y) in
          (inj 0 q : (int ⊕ ()))))))
      (fun from_either (e : (int ⊕ ())) : int .
        (cases e
          (case (ok : int) ok)
          (case (err : ()) 0)))
      (let (r : (int ⊕ ())) = (safe_div (10, 0)) in
      (app from_either r))
   |}

let incr_n =
  Parse.from_string_exn
    {|
      (fun incr_1 (r : (ref int)) : (ref int) .
        (split (old : int) (r1 : (ref int)) = (swap r 0) in
        (let (new : int) = (old + 1) in
        (let (p2 : (int ⊗ (ref int))) = (swap r1 new) in
        (split (_ : int) (r2 : (ref int)) = p2 in
        r2)))))

      (export fun incr_n (p : ((ref int) ⊗ int)) : int .
        (split (r : (ref int)) (n : int) = p in
        (if0 n then
          (free r)
        else
          (let (r1 : (ref int)) = (incr_1 r) in
          (let (n1 : int) = (n - 1) in
          (incr_n (r1, n1)))))))

      (let (r0 : (ref int)) = (new 10) in
      (app incr_n (r0, 3)))
    |}

let all =
  [
    ("simple_app_lambda", simple_app_lambda);
    ("add_one_program", add_one_program);
    ("add_tup_ref", add_tup_ref);
    ("print_10", print_10);
    ("factorial_program", factorial_program);
    ("safe_div", safe_div);
    ("incr_n", incr_n);
  ]
