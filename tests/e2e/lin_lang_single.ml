open! Core
module Expl = Test_examples.Lin_lang

let simple_tests =
  [
    ("one", "1", "1");
    ("add", "(6 + 7)", "13");
    ("tuple", "(1, 2, 3)", "[ 1, 2, 3 ]");
    ("nested arith", "((9 + 10) * 5)", "95");
    ("let bind", "(let (x : int) = 21 in x)", "21");
    ("app_id", "((lam (x : int) : int . x) 67)", "67");
    ( "sum-1",
      {|
      (cases (inj 0 22 : (sum int))
        (case (num : int) num))
      |},
      "22" );
    ( "sum-2",
      {|
      (cases (inj 1 (11, 11) : (sum int (prod int int)))
        (case (num : int) num)
        (case (tup : (prod int int)) 
          (split (a : int) (b : int) = tup in
          (+ a b))))
      |},
      "22" );
    ( "sum-4",
      {|
      (cases (inj 0 (tup 1) : (sum (prod int) (prod int int) (prod int int int) (prod int int int int)))
        (case (_ : (prod int)) 0)
        (case (_ : (prod int int)) 1)
        (case (_ : (prod int int int)) 2)
        (case (_ : (prod int int int int)) 3))
      |},
      "0" );
    ("if thn", "(if0 0 0 1)", "0");
    ("if els", "(if0 1 0 1)", "1");
    ("closure", Expl.closure, "10");
    ("closure call var", Expl.closure_call_var, "22");
    ("top-level triangle", Expl.triangle_tl, "55");
    ("top-level factorial", Expl.factorial_tl, "120");
    ("top-level mk_add", Expl.mk_add_tl, "25");
    ("expr mk_add", Expl.mk_add_expr, "25");
    ("expr mk_add3", Expl.mk_add3_expr, "54");
    ("new then free", "(free (new 10))", "10");
    ( "swap",
      {|
      (let (r : (ref int)) = (new 21) in
      (split (r' : (ref int)) (_ : int) = (swap r 67) in
      (free r')))
      |},
      "67" );
    ("incr_n", Expl.incr_n, "13");
    ("fold_unfold", Expl.fold_unfold, "0");
    ("heap_sum", Expl.heap_sum, "7");
    (* ("rec_peano_3", Expl.rec_peano_3, "3"); *)
    (* ("rec", {|

    |}, "") *)
    (* ("peano_3", Expl.peano_3, ""); *)
    (* ("boxed_list", Expl.boxed_list, ""); *)
    ("peano", Expl.peano, "13");
  ]
