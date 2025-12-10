open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Index

include Test_runner.Outputter.Make (struct
  include Test_runner.Outputter.DefaultConfig
  open Test_utils

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let syntax_pipeline x =
    x |> Index.Compile.compile_module |> or_fail_pp Index.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = IR.Module.pp
end)

let%expect_test "basic indexing" =
  let mk = Syntax.Module.make in
  output_syntax (mk ~main:(Let (("a", Int), Int 10, Var "a")) ());
  [%expect
    {|
      (let (<> : int) = 10 in
      <0:a>) |}];

  output_syntax
    (mk
       ~functions:
         [
           {
             export = true;
             name = "foo";
             param = ("x", Int);
             return = Int;
             body = Int 10;
           };
         ]
       ());
  [%expect
    {|
      (export fun foo (<> : int) : int .
        10) |}]

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    1
    -----------flat_tuple-----------
    (1, 2, 3, 4)
    -----------nested_tuple-----------
    ((1, 2), (3, 4))
    -----------single_sum-----------
    (inj 0 () : (⊕ (⊗)))
    -----------double_sum-----------
    (inj 1 15 : (⊕ (⊗) int))
    -----------arith_add-----------
    (9 + 10)
    -----------arith_sub-----------
    (67 - 41)
    -----------arith_mul-----------
    (42 × 10)
    -----------arith_div-----------
    (-30 ÷ 10)
    -----------app_ident-----------
    (app (λ (<> : int) : int .
           <0:x>) 10)
    -----------nested_arith-----------
    ((9 + 10) × 5)
    -----------let_bind-----------
    (let (<> : int) = 10 in
    <0:x>)
    -----------add_one_program-----------
    (export fun add-one (<> : int) : int .
      (<0:x> + 1))

    (app (coderef add-one) 42)
    -----------add_tup_ref-----------
    (let (<> : (ref int)) = (new 2) in
    (split (<> : int) (<> : (ref int)) = (1, <0:r>) in
    (let (<> : int) = (free <0:x2>) in
    (<2:x1> + <0:x2'>))))
    -----------print_10-----------
    (import (int ⊸ (⊗)) as print)

    (app (coderef print) 10)
    -----------closure-----------
    (let (<> : int) = 10 in
    (app (λ (<> : (⊗)) : int .
           <1:x>) ()))
    -----------factorial_program-----------
    (export fun factorial (<> : int) : int .
      (if0 <0:n> then 1 else
        (let (<> : int) = (<0:n> - 1) in
        (let (<> : int) = (app (coderef factorial) <0:n-sub1>) in
        (<2:n> × <0:rec-res>)))))

    (app (coderef factorial) 5)
    -----------safe_div-----------
    (fun safe_div (<> : (⊗ int int)) : (⊕ int (⊗)) .
      (split (<> : int) (<> : int) = <0:p> in
      (if0 <0:y> then (inj 1 () : (⊕ int (⊗))) else
        (let (<> : int) = (<1:x> ÷ <0:y>) in
        (inj 0 <0:q> : (⊕ int (⊗)))))))

    (fun from_either (<> : (⊕ int (⊗))) : int .
      (cases <0:e>
        (case (<> : int) <0:ok>)
        (case (<> : (⊗)) 0)))

    (let (<> : (⊕ int (⊗))) = (app (coderef safe_div) (10, 0)) in
    (app (coderef from_either) <0:r>))
    -----------incr_n-----------
    (fun incr_1 (<> : (ref int)) : (ref int) .
      (split (<> : (ref int)) (<> : int) = (swap <0:r> 0) in
      (let (<> : int) = (<0:old> + 1) in
      (split (<> : (ref int)) (<> : int) = (swap <2:r1> <0:new>) in
      <1:r2>))))

    (export fun incr_n (<> : (⊗ (ref int) int)) : int .
      (split (<> : (ref int)) (<> : int) = <0:p> in
      (if0 <0:n> then (free <1:r>) else
        (let (<> : (ref int)) = (app (coderef incr_1) <1:r>) in
        (let (<> : int) = (<1:n> - 1) in
        (app (coderef incr_n) (<1:r1>, <0:n1>)))))))

    (let (<> : (ref int)) = (new 10) in
    (app (coderef incr_n) (<0:r0>, 3)))
    -----------fix_factorial[invalid]-----------
    (let (<> : (((int ⊸ int) ⊸ (int ⊸ int)) ⊸ (int ⊸ int))) =
      (λ (<> : ((int ⊸ int) ⊸ (int ⊸ int))) : (int ⊸ int) .
        (let (<> : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int))) =
          (λ (<> : (rec [] ([0:a] ⊸ (int ⊸ int)))) : (int ⊸ int) .
            (let (<> : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int))) =
              (unfold (rec [] ([0:a] ⊸ (int ⊸ int))) <0:x>) in
            (let (<> : (int ⊸ int)) = (app <0:ux> <1:x>) in
            (app <3:f> <0:xx>))))
          in
        (app <0:omega> (fold (rec [] ([0:a] ⊸ (int ⊸ int))) <0:omega>))))
      in
    (let (<> : (int ⊸ int)) =
      (app <0:fix>
        (λ (<> : (int ⊸ int)) : (int ⊸ int) .
          (λ (<> : int) : int .
            (if0 <0:n> then 1 else
              (let (<> : int) = (<0:n> - 1) in
              (let (<> : int) = (app <2:rec> <0:n-sub1>) in
              (<2:n> × <0:rec-res>)))))))
      in
    (app <0:factorial> 5)))
    -----------unboxed_list[invalid]-----------
    (fun map_int (<> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) :
      (rec [] (⊕ (⊗) (⊗ int [0:α]))) .
      (split (<> : (int ⊸ int)) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
        <0:p> in
      (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
        (cases (unfold (rec [] (⊕ (⊗) (⊗ int [0:α]))) <0:lst>)
          (case (<> : (⊗))
            (inj 0 <0:nil> :
              (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
          (case (<> : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))
            (split (<> : int) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
              <0:cons> in
            (inj 1 ((app <4:f> <1:hd>), (app (coderef map_int) (<4:f>, <0:tl>))) :
              (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))))
          ))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
      (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
        (inj 0 () : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
      in
    (app (coderef map_int) ((λ (<> : int) : int .
                              (<0:x> + 1)), <0:lst>)))
    -----------boxed_list-----------
    (fun map_int
      (<> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) :
      (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))) .
      (split (<> : (int ⊸ int))
        (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) = <0:p> in
      (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
        (cases (unfold (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))) <0:lst>)
          (case (<> : (⊗))
            (inj 0 <0:nil> :
              (⊕ (⊗)
                (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
          (case (<> : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
            (split (<> : int)
              (<> : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) = <0:cons>
              in
            (inj 1
              ((app <4:f> <1:hd>),
                (new (app (coderef map_int) (<4:f>, (free <0:tl>)))))
              :
              (⊕ (⊗)
                (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))))
          ))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) =
      (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
        (inj 1
          (5,
            (new
            (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
              (inj 0 () :
                (⊕ (⊗)
                  (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))))
          :
          (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
      in
    (app (coderef map_int) ((λ (<> : int) : int .
                              (<0:x> + 1)), <0:lst>)))
    -----------peano_3-----------
    (fold (rec [] (⊕ (⊗) (ref [0:a])))
      (inj 1
        (new
        (fold (rec [] (⊕ (⊗) (ref [0:a])))
          (inj 1
            (new
            (fold (rec [] (⊕ (⊗) (ref [0:a])))
              (inj 1
                (new
                (fold (rec [] (⊕ (⊗) (ref [0:a])))
                  (inj 0 () : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))))
                : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))))
            : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))))
        : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a])))))))
    -----------peano-----------
    (fun add
      (<> : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) :
      (rec [] (⊕ (⊗) (ref [0:a]))) .
      (split (<> : (rec [] (⊕ (⊗) (ref [0:a]))))
        (<> : (rec [] (⊕ (⊗) (ref [0:a])))) = <0:p> in
      (cases (unfold (rec [] (⊕ (⊗) (ref [0:a]))) <1:left>)
        (case (<> : (⊗)) <1:right>)
        (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
          (fold (rec [] (⊕ (⊗) (ref [0:a])))
            (inj 1 (new (app (coderef add) ((free <0:succ>), <1:right>))) :
              (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a])))))))))))

    (fun from-int (<> : int) : (rec [] (⊕ (⊗) (ref [0:a]))) .
      (fold (rec [] (⊕ (⊗) (ref [0:a])))
        (if0 <0:int>
          then (inj 0 () : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a])))))) else
          (inj 1 (new (app (coderef from-int) (<0:int> - 1))) :
            (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a])))))))))

    (fun to-int (<> : (rec [] (⊕ (⊗) (ref [0:a])))) : int .
      (cases (unfold (rec [] (⊕ (⊗) (ref [0:a]))) <0:peano>)
        (case (<> : (⊗)) 0)
        (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
          (1 + (app (coderef to-int) (free <0:succ>))))))

    (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) = (app (coderef from-int) 6) in
    (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) = (app (coderef from-int) 7) in
    (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
      (app (coderef add) (<1:six>, <0:seven>)) in
    (app (coderef to-int) <0:sum>))))
    -----------mini_zip-----------
    (fun add1 (<> : int) : int .
      (<0:x> + 1))

    (export fun typle_add1 (<> : (⊗ int int)) : (⊗ int int) .
      (split (<> : int) (<> : int) = <0:x> in
      ((app (coderef add1) <1:x1>), (app (coderef add1) <0:x2>))))

    (fun mini_zip_specialized (<> : (⊗ (ref int) (ref (ref int)))) :
      (ref (⊗ int (ref int))) .
      (split (<> : (ref int)) (<> : (ref (ref int))) = <0:p> in
      (new ((free <1:a>), (free <0:b>))))) |}]
