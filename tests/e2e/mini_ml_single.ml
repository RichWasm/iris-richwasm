open! Core
open! Test_examples.Mini_ml

let simple_tests =
  [
    (* the output is the raw wasm value. I31s are tagged *)
    ("one", "1", "2");
    ("add", "(op + 1 2)", "6");
    ("add 2", "(op + 2 3)", "10");
    ("arithmetic", "(op * 3 (op + 1 2))", "18");
    ("basic let", "(let (x : int) 1 x)", "2");
    (* ( "closure",
      {|
        (let (x : int) 1
          (let (f : (() (*) -> int))
            (fun () (_ : (*)) : int
              x)
            (app f () (tup))))
      |},
      "" ); *)
    ("if true", "(if 0 3 2)", "6");
    ("if false", "(if 1 2 3)", "6");
    (* TODO: better output printer for pointers *)
    ("tuple", "(tup 1 2)", "3");
    (* 3 is the first root ptr *)
    ("tuple proj", "(proj 1 (tup 1 2))", "4");
    ("ref deref", "(! (new 3))", "6");
    (* ("app", "(app (fun () (_ : (*)) : int 1) () (tup))", "2"); *)
    (* ( "ref assign",
      {|
      (let (r : (ref int)) (new 3)
        (let (_ : (*)) (assign r 8)
          (! r)))
    |},
      "1" ); *)
    (* The tests below exercise function application and closures. They fail
       today because mini-ml's compile_type Prod uses `New + Cast` from
       `Ser (Prod)` to `Struct`, and the richwasm cast rule requires uniform
       refflag across struct fields. A closure-call tuple of (env_ref, i31)
       mixes gcrefs and norefs, so the cast typecheck fails. *)
    ( "app inline identity",
      "(app (fun () (x : int) : int x) () 5)",
      "10" );
    ( "app inline lambda",
      "(app (fun () (x : int) : int (op + x 1)) () 5)",
      "12" );
    ( "app top-level function",
      {|
        (export (add1 : (() int -> int))
          (fun () (x : int) : int (op + x 1)))
        (app add1 () 5)
      |},
      "12" );
    ( "top-level identity",
      {|
        (export (id : (() int -> int))
          (fun () (x : int) : int x))
        (app id () 5)
      |},
      "10" );
    ( "closure captures int",
      {|
        (let (n : int) 3
          (let (f : (() int -> int))
            (fun () (x : int) : int (op + x n))
            (app f () 5)))
      |},
      "16" );
    ( "two top-level functions",
      {|
        (export (double : (() int -> int))
          (fun () (x : int) : int (op + x x)))
        (export (add3 : (() int -> int))
          (fun () (x : int) : int (op + x 3)))
        (app double () (app add3 () 4))
      |},
      "28" );
  ]
