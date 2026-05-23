open! Core
open! Test_examples.Mini_ml

let i31 x = sprintf "%i" (x * 2)

let simple_tests =
  [
    (* the output is the raw wasm value. I31s are tagged *)
    ("one", "1", i31 1);
    ("add", "(op + 1 2)", i31 (1 + 2));
    ("add 2", "(op + 2 3)", i31 (2 + 3));
    ("arithmetic", "(op * 3 (op + 1 2))", i31 (3 * (1 + 2)));
    ("basic let", "(let (x : int) 1 x)", i31 1);
    ( "closure",
      {|
        (let (x : int) 1
          (let (f : (() (*) -> int))
            (fun () (_ : (*)) : int
              x)
            (app f () (tup))))
      |},
      i31 1 );
    ("if true", "(if 0 3 2)", i31 3);
    ("if false", "(if 1 2 3)", i31 3);
    (* TODO: better output printer for pointers *)
    (* 3 is the first root ptr *)
    ("tuple", "(tup 1 2)", "3");
    ("tuple proj", "(proj 1 (tup 1 2))", i31 2);
    ("ref deref", "(! (new 3))", i31 3);
    ("app", "(app (fun () (_ : (*)) : int 1) () (tup))", i31 1);
    ( "ref assign",
      {|
      (let (r : (ref int)) (new 3)
        (let (_ : (*)) (assign r 8)
          (! r)))
      |},
      i31 8 );
    ("app inline identity", "(app (fun () (x : int) : int x) () 5)", i31 5);
    ( "app inline lambda",
      "(app (fun () (x : int) : int (op + x 1)) () 5)",
      i31 (5 + 1) );
    ( "app top-level function",
      {|
        (export (add1 : (() int -> int))
          (fun () (x : int) : int (op + x 1)))
        (app add1 () 5)
      |},
      i31 (5 + 1) );
    ( "top-level identity",
      {|
        (export (id : (() int -> int))
          (fun () (x : int) : int x))
        (app id () 5)
      |},
      i31 5 );
    ( "closure captures int",
      {|
        (let (n : int) 3
          (let (f : (() int -> int))
            (fun () (x : int) : int (op + x n))
            (app f () 5)))
      |},
      i31 (5 + 3) );
    ( "two top-level functions",
      {|
        (export (double : (() int -> int))
          (fun () (x : int) : int (op + x x)))
        (export (add3 : (() int -> int))
          (fun () (x : int) : int (op + x 3)))
        (app double () (app add3 () 4))
      |},
      i31 ((4 + 3) * 2) );
  ]
