open! Core
open! Test_examples.Mini_ml

(* results are rendered structurally by the runtime host (tests/support/walker.ts) *)
let i31 x = sprintf "%i" x

(* A well-typed cons-list `rec b. unit + (int * b)`: nil = inj0 unit,
   cons h t = inj1 (h, t). (The examples' [poly_len] can't be reused — it is
   independently ill-typed: its folds' arguments don't match the unfolded
   type.) Building the source via sprintf keeps the nested annotations honest. *)
let list_rec = "(rec (b) (+ (*) (* int b)))"
let list_sum = "(+ (*) (* int (rec (b) (+ (*) (* int b)))))"
let nil = sprintf "(fold %s (inj 0 (tup) : %s))" list_rec list_sum
let cons h t = sprintf "(fold %s (inj 1 (tup %i %s) : %s))" list_rec h t list_sum

(* Monomorphic recursive [length]: exercises [cases] (sum elimination) over the
   unfolded list together with a self-call on the tail. *)
let len_fn =
  sprintf
    {|
      (export (len : (() %s -> int))
        (fun () (x : %s) : int
          (cases (unfold x)
            ((_ : (*)) 0)
            ((y : (* int %s))
              (op + 1 (app len () (proj 1 y)))))))
    |}
    list_rec list_rec list_rec

let simple_tests =
  [
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
    ("tuple", "(tup 1 2)", "(tup 1 2)");
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
    ("tuple 3", "(tup 1 2 3)", "(tup 1 2 3)");
    ("tuple nested", "(tup (tup 1 2) (tup 3 4))", "(tup (tup 1 2) (tup 3 4))");
    ("tuple deep", "(tup 1 (tup 2 (tup 3 4)))", "(tup 1 (tup 2 (tup 3 4)))");
    ( "shared tuple",
      "(let (p : (* int int)) (tup 1 2) (tup p p))",
      "(tup (tup 1 2) (tup 1 2))" );
    ("sum none", "(inj 0 (tup) : (+ (*) int))", "(inj 0)");
    ("sum some", "(inj 1 42 : (+ (*) int))", "(inj 1 42)");
    ( "sum of tuple",
      "(inj 1 (tup 1 2) : (+ (*) (* int int)))",
      "(inj 1 (tup 1 2))" );
    ("sum in tuple", "(tup (inj 1 7 : (+ (*) int)) 9)", "(tup (inj 1 7) 9)");
    ("ref cell", "(new 5)", "(ref 5)");
    ("ref to tuple", "(new (tup 1 2))", "(ref (tup 1 2))");
    ("ref in tuple", "(tup (new 1) 2)", "(tup (ref 1) 2)");
    ( "updated ref",
      "(let (r : (ref int)) (new 3) (let (_ : (*)) (assign r 8) r))",
      "(ref 8)" );
    ("unit in tuple", "(tup (tup) 5)", "(tup (tup) 5)");
    ( "cases some",
      "(cases (inj 1 42 : (+ (*) int)) ((_ : (*)) 0) ((v : int) v))",
      i31 42 );
    ( "cases none",
      "(cases (inj 0 (tup) : (+ (*) int)) ((_ : (*)) 7) ((v : int) v))",
      i31 7 );
  ]
