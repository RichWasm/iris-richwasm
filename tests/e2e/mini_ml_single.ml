open! Core
open Test_examples.Mini_ml

let simple_tests =
  [
    (* the output is the raw wasm value. I31s are tagged *)
    ("one", "1", "2");
    ("add", "(op + 1 2)", "6");
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
  ]
