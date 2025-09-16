open Richwasm_lin_lang.Syntax
open Format

let%expect_test "pretty prints examples" =
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
  let fmt = Format.std_formatter in
  Format.pp_set_margin fmt 120;
  Format.pp_set_max_indent fmt 80;
  List.iter
    (fun (n, m) -> printf "-----------%s-----------@.%a@." n Module.pp m)
    examples;
  [%expect {|
    -----------add_one_program-----------
    export let (add_one : (int ⊸ int)) = (λ (x : int) : int . (x + 1))

    (app add_one 42)
    -----------swap_pair_program-----------
    export let (swap : ((int ⊗ int) ⊸ (int ⊗ int))) =
      (λ (p : (int ⊗ int)) : (int ⊗ int) . let ((x : int), (y : int)) = p in (y, x))

    (app swap (1, 2))
    -----------compose_program-----------
    export let (compose : ((int ⊸ int) ⊸ ((int ⊸ int) ⊸ (int ⊸ int)))) =
      (λ (f : (int ⊸ int)) : ((int ⊸ int) ⊸ (int ⊸ int)) .
        (λ (g : (int ⊸ int)) : (int ⊸ int) .
          (λ (x : int) : int . let (g_result : int) = (app g x) in (app f g_result))))



    -----------reference_example-----------
    let (test_ref : int) =
      let (r : (ref int)) = (new 10) in let (old_val : int) = (swap r 20) in let (_ : int) = (free r) in old_val

    test_ref
    -----------factorial_program-----------
    export let (factorial : (int ⊸ int)) =
      (λ (n : int) : int .
        if n then 1 else
          let (n_minus_1 : int) = (n - 1) in
            let (rec_result : int) = (app factorial n_minus_1) in
              let (final_result : int) = (n × rec_result) in final_result)


    (app factorial 5)
    -----------module_with_imports-----------
    (import external_inc : (int ⊸ int))
    (import external_add : ((int ⊗ int) ⊸ int))

    export let (double_inc : (int ⊸ int)) =
      (λ (x : int) : int . let (first_inc : int) = (app external_inc x) in (app external_inc first_inc))

    (app double_inc 5)
    -----------complex_example-----------
    export let (process_pair : ((int ⊗ int) ⊸ int)) =
      (λ (input : (int ⊗ int)) : int .
        let ((a : int), (b : int)) = input in
          let (sum : int) = (a + b) in
            let (r1 : (ref int)) = (new sum) in
              let (product : int) = (a × b) in
                let (r2 : (ref int)) = (new product) in
                  let (sum_val : int) = (swap r1 0) in
                    let (prod_val : int) = (swap r2 0) in
                      let (_1 : int) = (free r1) in
                        let (_2 : int) = (free r2) in let (final_result : int) = (sum_val + prod_val) in final_result)


    (app process_pair (3, 4))
    -----------closure_example-----------
    export let (make_adder : (int ⊸ (int ⊸ int))) = (λ (n : int) : (int ⊸ int) . (λ (x : int) : int . (n + x)))

    let (add5 : (int ⊸ int)) = (app make_adder 5) in (app add5 10)
  |}]
