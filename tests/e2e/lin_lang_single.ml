open! Core

let simple_tests =
  [
    ("one", "1", "1");
    ("add", "(6 + 7)", "13");
    ("tuple", "(1, 2, 3)", "[ 1, 2, 3 ]");
    ("nested_arith", "((9 + 10) * 5)", "95");
    ("let_bind", "(let (x : int) = 21 in x)", "21");
    ("app_id", "((lam (x : int) : int . x) 67)", "67");
  ]
