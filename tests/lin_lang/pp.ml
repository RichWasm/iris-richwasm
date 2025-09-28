open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Syntax

let%expect_test "pretty prints examples" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let examples : (string * Module.t) list =
    Examples.
      [
        ("add_one_program", add_one_program);
        ("swap_pair_program", swap_pair_program);
        ("compose_program", compose_program);
        ("reference_example", reference_example);
        ("factorial_program", factorial_program);
        ("module_with_imports", module_with_imports);
        ("complex_example", complex_example);
        ("closure_example", closure_example);
      ]
  in
  List.iter
    ~f:(fun (n, m) -> printf "-----------%s-----------@.%a@." n Module.pp m)
    examples;
  [%expect
    {|
    -----------add_one_program-----------
    (export fun add_one (x : int) : int . (x + 1))

    (app add_one 42)
    -----------swap_pair_program-----------
    (export fun swap (p : (int ⊗ int)) : (int ⊗ int) .
      (letprod ((x : int), (y : int)) = p in
      (y, x)))

    (app swap (1, 2))
    -----------compose_program-----------
    (export fun compose (f : (int ⊸ int)) : ((int ⊸ int) ⊸ (int ⊸ int)) .
      (λ (g : (int ⊸ int)) : (int ⊸ int) .
        (λ (x : int) : int .
          (let (g_result : int) = (app g x) in
          (app f g_result)))))



    -----------reference_example-----------
    (let (r : (ref int)) = (new 10) in
    (let (old_val : int) = (swap r 20) in
    (let (_ : int) = (free r) in
    old_val)))
    -----------factorial_program-----------
    (export fun factorial (n : int) : int .
      (if n then 1 else
        (let (n_minus_1 : int) = (n - 1) in
        (let (rec_result : int) = (app factorial n_minus_1) in
        (let (final_result : int) = (n × rec_result) in
        final_result)))))


    (app factorial 5)
    -----------module_with_imports-----------
    (import (int ⊸ int) as external_inc)
    (import ((int ⊗ int) ⊸ int) as external_add)

    (export fun double_inc (x : int) : int .
      (let (first_inc : int) = (app external_inc x) in
      (app external_inc first_inc)))

    (app double_inc 5)
    -----------complex_example-----------
    (export fun process_pair (input : (int ⊗ int)) : int .
      (letprod ((a : int), (b : int)) = input in
      (let (sum : int) = (a + b) in
      (let (r1 : (ref int)) = (new sum) in
      (let (product : int) = (a × b) in
      (let (r2 : (ref int)) = (new product) in
      (let (sum_val : int) = (swap r1 0) in
      (let (prod_val : int) = (swap r2 0) in
      (let (_1 : int) = (free r1) in
      (let (_2 : int) = (free r2) in
      (let (final_result : int) = (sum_val + prod_val) in
      final_result)))))))))))

    (app process_pair (3, 4))
    -----------closure_example-----------
    (export fun make_adder (n : int) : (int ⊸ int) .
      (λ (x : int) : int .
        (n + x)))


    (let (add5 : (int ⊸ int)) = (app make_adder 5) in
    (app add5 10))
  |}]
