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
    ("if thn", "(if0 0 0 1)", "0");
    ("if els", "(if0 1 0 1)", "1");
    ("closure", Expl.closure, "10");
    ("closure call var", Expl.closure_call_var, "22");
    ("top-level triangle", Expl.triangle_tl, "55");
    ("top-level factorial", Expl.factorial_tl, "120");
    ("top-level mk_add", Expl.mk_add_tl, "25");
  ]
