open! Base
open Richwasm_mini_ml
open Parse

let add_one =
  from_string_exn
    {|
      (export (add1 : (() int -> int))
        (fun () (x : int) : int
          (op + x 1)))
    |}

let id =
  from_string_exn
    {|
      (export (id : ((a) a -> a))
        (fun (a) (x : a) : a
          x))
    |}

let apply_id =
  from_string_exn
    {|
      (export (id : ((a) a -> a))
        (fun (a) (x : a) : a
          x))
      (app id (int) 42)
    |}

let opt_case =
  from_string_exn
    {|
      (let (option : (+ (*) int))
        (inj 1 42 : (+ (*) int))
        (cases option
          ((_ : (*)) 0)
          ((v : int) v)))
    |}

(* A list is `rec b. unit + (a * b)`: nil = inj0 unit, cons h t = inj1 (h, t).
   `len` unfolds, and in the cons case recurses on the tail `proj 1 y`. *)
let poly_len_src =
  {|
      (export (len : ((a) (rec (b) (+ (*) (* a b))) -> int))
        (fun (a) (x : (rec (b) (+ (*) (* a b)))) : int
          (cases (unfold x)
            ((_ : (*)) 0)
            ((y : (* a (rec (b) (+ (*) (* a b)))))
              (op + 1 (app len (a) (proj 1 y)))))))

      (app len (int)
        (fold (rec (b) (+ (*) (* int b)))
          (inj 1
            (tup 1
              (fold (rec (b) (+ (*) (* int b)))
                (inj 0 (tup) : (+ (*) (* int (rec (b) (+ (*) (* int b))))))))
            : (+ (*) (* int (rec (b) (+ (*) (* int b))))))))
    |}

let poly_len = from_string_exn poly_len_src

(* [apply] returns a polymorphic call's result instantiated at its own type param (a bound-var result). *)
let poly_id_apply_src =
  {|
      (export (id : ((a) a -> a))
        (fun (a) (x : a) : a x))
      (export (apply : ((a) a -> a))
        (fun (a) (x : a) : a (app id (a) x)))

      (app apply (int) 5)
    |}

let poly_id_apply = from_string_exn poly_id_apply_src

let mini_zip =
  from_string_exn
    {|
      (export (mini_zip : ((a b) (* (ref a) (ref b)) -> (ref (* a b))))
        (fun (a b) (x : (* (ref a) (ref b))) : (ref (* a b))
          (new (tup (! (proj 0 x)) (! (proj 1 x))))))
    |}

let closure_simpl =
  from_string_exn
    {|
      (let (x : int) 1
        (let (f : (() (*) -> int))
          (fun () (_ : (*)) : int
            x)
          (app f () (tup))))
    |}

let closure_complex =
  from_string_exn
    {|
      (let (x : int) 1
        (let (f : (() int -> int))
          (fun () (y : int) : int
            (op + x y))
          (let (g : (() int -> int))
            (fun () (z : int) : int
              (op + (app f () z) x))
            (app g () 3))))
    |}

let assign =
  from_string_exn
    {|
      (let (r : (ref int)) (new 0)
        (let (_ : (*)) (assign r 1)
          (! r)))
    |}

let simple =
  [
    ("one", "1");
    ("tuple", "(tup 1 2 3 4)");
    ("tuple_nested", "(tup (tup 1 2) (tup 3 4))");
    ("tuple_project", "(proj 1 (tup 42 7))");
    ("utuple", "(tup# 1 2)");
    ("utuple_split", "(split# ((a : int) (b : int)) (tup# 42 7) b)");
    ( "utuple_let",
      "(let (p : (*# int int)) (tup# 1 2) (split# ((a : int) (b : int)) p a))"
    );
    ("utuple_in_tuple", "(tup (tup# 1 2) 3)");
    ("utuple_of_tuple", "(tup# (tup 1 2) 3)");
    ("utuple_ref", "(! (new (tup# 1 2)))");
    ( "utuple_fn",
      {|
        (app (fun () (x : (*# int int)) : int
               (split# ((a : int) (b : int)) x a))
          () (tup# 5 6))
      |}
    );
    ( "utuple_ret",
      {|
        (split# ((a : int) (b : int))
                (app (fun () (x : int) : (*# int int) (tup# x 9)) () 4)
          b)
      |}
    );
    ( "lin_make",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (app mk () 5)
      |}
    );
    ( "lin_deref",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (! (app mk () 5))
      |}
    );
    ( "lin_assign",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (assign (app mk () 5) 8)
      |}
    );
    ( "lin_let",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (let (r : (lin (ref int))) (app mk () 3)
          (assign r 9))
      |}
    );
    ( "lin_roundtrip",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (split# ((r : (lin (ref int))) (old : int))
                (! (assign (app mk () 3) 8))
          (tup# r old))
      |}
    );
    ( "lin_reuse_rejected",
      {|
        (import (mk : (() int -> (lin (ref int)))))
        (let (r : (lin (ref int))) (app mk () 3)
          (tup# (assign r 8) (assign r 9)))
      |}
    );
    ("sum_unit", "(inj 0 (tup) : (+ (*)))");
    ("sum_option", "(inj 1 15 : (+ (*) int))");
    ("basic_if", "(if 0 1 2)");
    ("add", "(op + 1 2)");
    ("sub", "(op - 1 2)");
    ("mul", "(op * 1 2)");
    ("div", "(op / 1 2)");
    ("math", "(op / (op * 2 6) 3)");
    ("basic_let", "(let (x : int) 10 x)");
    ("return_one", "(fun () (_ : (*)) : int 1)");
    ("iife", "(app (fun () (_ : (*)) : int 1) () (tup))");
    ("---------", "(app (fun () (x : int) : int x) () 5)");
  ]
  |> List.map ~f:(fun (n, src) -> (n, from_string_exn src))

let all =
  simple
  @ [
      ("add_one", add_one);
      ("id", id);
      ("assign", assign);
      ("apply_id", apply_id);
      ("opt_case", opt_case);
      ("poly_len", poly_len);
      ("poly_id_apply", poly_id_apply);
      ("mini_zip", mini_zip);
      ("closure_simpl", closure_simpl);
      ("closure_complex", closure_complex);
    ]
