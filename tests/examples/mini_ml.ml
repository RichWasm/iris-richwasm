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

let poly_len =
  from_string_exn
    {|
      (export (len : ((a) (rec (b) (+ (*) (+ a b))) -> int))
        (fun (a) (x : (rec (b) (+ (*) (+ a b)))) : int
          (cases (unfold x)
            ((_ : (*)) 0)
            ((y : (+ a (rec (b) (+ (*) (+ a b)))))
              (op + 1 (app len (a) (fold (rec (b) (+ (*) (+ a b))) y)))))))

      (app len (int)
        (fold (rec (b) (+ (*) (+ int b)))
          (inj 1 (tup 1 (fold (rec (b) (+ (*) (+ int b)))
            (inj 0 (tup) : (+ (*) (rec (b) (+ (*) (+ int b)))))))
            : (+ (*) (+ int (rec (b) (+ (*) (+ int b))))))))
    |}

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

let simple =
  [
    ("one", "1");
    ("tuple", "(tup 1 2 3 4)");
    ("tuple_nested", "(tup (tup 1 2) (tup 3 4))");
    ("tuple_project", "(proj 1 (tup 42 7))");
    ("sum_unit", "(inj 0 (tup) : (+ (*)))");
    ("sum_option", "(inj 1 15 : (+ (*) int))");
    ("add", "(op + 1 2)");
    ("sub", "(op - 1 2)");
    ("mul", "(op * 1 2)");
    ("div", "(op / 1 2)");
    ("math", "(op / (op * 2 6) 3)");
    ("basic_let", "(let (x : int) 10 x)");
    ("return_one", "(fun () (_ : (*)) : int 1)");
  ]
  |> List.map ~f:(fun (n, src) -> (n, from_string_exn src))

let all =
  simple
  @ [
      ("add_one", add_one);
      ("id", id);
      ("apply_id", apply_id);
      ("opt_case", opt_case);
      ("poly_len", poly_len);
      ("mini_zip", mini_zip);
      ("closure_simpl", closure_simpl);
      ("closure_complex", closure_complex);
    ]
