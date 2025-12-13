open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Typecheck

include Test_runner.Outputter.Make (struct
  include Test_runner.Outputter.DefaultConfig
  open Test_utils

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let syntax_pipeline x =
    x
    |> Index.Compile.compile_module
    |> or_fail_pp Index.Err.pp
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = IR.Module.pp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    (1 : int)
    -----------flat_tuple-----------
    (tup (1 : int) (2 : int) (3 : int) (4 : int) : (⊗ int int int int))
    -----------nested_tuple-----------
    (tup (tup (1 : int) (2 : int) : (⊗ int int))
       (tup (3 : int) (4 : int) : (⊗ int int))
     : (⊗ (⊗ int int) (⊗ int int)))
    -----------single_sum-----------
    (inj 0 (tup : (⊗)) : (⊕ (⊗)))
    -----------double_sum-----------
    (inj 1 (15 : int) : (⊕ (⊗) int))
    -----------arith_add-----------
    (+ (9 : int) (10 : int) : int)
    -----------arith_sub-----------
    (- (67 : int) (41 : int) : int)
    -----------arith_mul-----------
    (× (42 : int) (10 : int) : int)
    -----------arith_div-----------
    (÷ (-30 : int) (10 : int) : int)
    -----------app_ident-----------
    (app (λ (<> : int) : int .
            (<0:x> : int)
          : (int ⊸ int)) (10 : int) : int)
    -----------nested_arith-----------
    (× (+ (9 : int) (10 : int) : int) (5 : int) : int)
    -----------let_bind-----------
    (let (<> : int) = (10 : int) in
     (<0:x> : int)
     : int)
    -----------add_one_program-----------
    (export fun add-one (<> : int) : int .
      (+ (<0:x> : int) (1 : int) : int))

    (app (coderef add-one : (int ⊸ int)) (42 : int) : int)
    -----------add_tup_ref-----------
    (let (<> : (ref int)) = (new (2 : int) : (ref int)) in
     (split (<> : int) (<> : (ref int)) =
        (tup (1 : int) (<0:r> : (ref int)) : (⊗ int (ref int))) in
      (let (<> : int) = (free (<0:x2> : (ref int)) : int) in
       (+ (<2:x1> : int) (<0:x2'> : int) : int)
       : int) : int)
     : int)
    -----------print_10-----------
    (import (int ⊸ (⊗)) as print)

    (app (coderef print : (int ⊸ (⊗))) (10 : int) : (⊗))
    -----------closure-----------
    (let (<> : int) = (10 : int) in
     (app (λ (<> : (⊗)) : int .
             (<1:x> : int)
           : ((⊗) ⊸ int))
        (tup : (⊗)) : int)
     : int)
    -----------closure_call_var-----------
    (let (<> : int) = (21 : int) in
     (let (<> : int) = (1 : int) in
      (app
         (λ (<> : int) : int .
            (+ (<0:x> : int) (<1:add-amount> : int) : int)
          : (int ⊸ int))
         (<1:input> : int) : int)
      : int)
     : int)
    -----------triangle_tl-----------
    (fun triangle (<> : int) : int .
      (if0 (<0:n> : int)
       then (0 : int)
       else
         (+ (<0:n> : int)
            (app (coderef triangle : (int ⊸ int))
               (- (<0:n> : int) (1 : int) : int) : int)
            : int)
       : int))

    (app (coderef triangle : (int ⊸ int)) (10 : int) : int)
    -----------factorial_tl-----------
    (export fun factorial (<> : int) : int .
      (if0 (<0:n> : int)
       then (1 : int)
       else
         (let (<> : int) = (- (<0:n> : int) (1 : int) : int) in
          (let (<> : int) =
             (app (coderef factorial : (int ⊸ int)) (<0:n-sub1> : int) : int) in
           (× (<2:n> : int) (<0:rec-res> : int) : int)
           : int)
          : int)
       : int))

    (app (coderef factorial : (int ⊸ int)) (5 : int) : int)
    -----------safe_div-----------
    (fun safe_div (<> : (⊗ int int)) : (⊕ int (⊗)) .
      (split (<> : int) (<> : int) = (<0:p> : (⊗ int int)) in
       (if0 (<0:y> : int)
        then (inj 1 (tup : (⊗)) : (⊕ int (⊗)))
        else
          (let (<> : int) = (÷ (<1:x> : int) (<0:y> : int) : int) in
           (inj 0 (<0:q> : int) : (⊕ int (⊗)))
           : (⊕ int (⊗)))
        : (⊕ int (⊗)))
      : (⊕ int (⊗))))

    (fun from_either (<> : (⊕ int (⊗))) : int .
      (cases (<0:e> : (⊕ int (⊗)))
         (case (<> : int) (<0:ok> : int))
         (case (<> : (⊗)) (0 : int))
       : int))

    (let (<> : (⊕ int (⊗))) =
       (app (coderef safe_div : ((⊗ int int) ⊸ (⊕ int (⊗))))
          (tup (10 : int) (0 : int) : (⊗ int int)) : (⊕ int (⊗)))
       in
     (app (coderef from_either : ((⊕ int (⊗)) ⊸ int))
        (<0:r> : (⊕ int (⊗))) : int)
     : int)
    -----------incr_n-----------
    (fun incr_1 (<> : (ref int)) : (ref int) .
      (split (<> : (ref int)) (<> : int) =
         (swap (<0:r> : (ref int)) (0 : int) : (⊗ (ref int) int)) in
       (let (<> : int) = (+ (<0:old> : int) (1 : int) : int) in
        (split (<> : (ref int)) (<> : int) =
           (swap (<2:r1> : (ref int)) (<0:new> : int) : (⊗ (ref int) int)) in
         (<1:r2> : (ref int)) : (ref int))
        : (ref int))
      : (ref int)))

    (export fun incr_n (<> : (⊗ (ref int) int)) : int .
      (split (<> : (ref int)) (<> : int) = (<0:p> : (⊗ (ref int) int)) in
       (if0 (<0:n> : int)
        then (free (<1:r> : (ref int)) : int)
        else
          (let (<> : (ref int)) =
             (app (coderef incr_1 : ((ref int) ⊸ (ref int))) (<1:r> : (ref int))
                : (ref int))
             in
           (let (<> : int) = (- (<1:n> : int) (1 : int) : int) in
            (app (coderef incr_n : ((⊗ (ref int) int) ⊸ int))
               (tup (<1:r1> : (ref int)) (<0:n1> : int) : (⊗ (ref int) int))
               : int)
            : int)
           : int)
        : int)
      : int))

    (let (<> : (ref int)) = (new (10 : int) : (ref int)) in
     (app (coderef incr_n : ((⊗ (ref int) int) ⊸ int))
        (tup (<0:r0> : (ref int)) (3 : int) : (⊗ (ref int) int)) : int)
     : int)
    -----------fix_factorial[invalid]-----------
    (let (<> : (((int ⊸ int) ⊸ (int ⊸ int)) ⊸ (int ⊸ int))) =
       (λ (<> : ((int ⊸ int) ⊸ (int ⊸ int))) : (int ⊸ int) .
          (let (<> : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int))) =
             (λ (<> : (rec [] ([0:a] ⊸ (int ⊸ int)))) : (int ⊸ int) .
                (let (<> : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
                   =
                   (unfold (rec [] ([0:a] ⊸ (int ⊸ int)))
                      (<0:x> : (rec [] ([0:a] ⊸ (int ⊸ int))))
                      : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
                   in
                 (let (<> : (int ⊸ int)) =
                    (app
                       (<0:ux>
                          : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
                       (<1:x> : (rec [] ([0:a] ⊸ (int ⊸ int)))) : (int ⊸ int))
                    in
                  (app (<3:f> : ((int ⊸ int) ⊸ (int ⊸ int)))
                     (<0:xx> : (int ⊸ int)) : (int ⊸ int))
                  : (int ⊸ int))
                 : (int ⊸ int))
              : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
             in
           (app
              (<0:omega> : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
              (fold (rec [] ([0:a] ⊸ (int ⊸ int)))
                 (<0:omega>
                    : ((rec [] ([0:a] ⊸ (int ⊸ int))) ⊸ (int ⊸ int)))
                 : (rec [] ([0:a] ⊸ (int ⊸ int))))
              : (int ⊸ int))
           : (int ⊸ int))
        : (((int ⊸ int) ⊸ (int ⊸ int)) ⊸ (int ⊸ int)))
       in
     (let (<> : (int ⊸ int)) =
        (app (<0:fix> : (((int ⊸ int) ⊸ (int ⊸ int)) ⊸ (int ⊸ int)))
           (λ (<> : (int ⊸ int)) : (int ⊸ int) .
              (λ (<> : int) : int .
                 (if0 (<0:n> : int)
                  then (1 : int)
                  else
                    (let (<> : int) = (- (<0:n> : int) (1 : int) : int) in
                     (let (<> : int) =
                        (app (<2:rec> : (int ⊸ int)) (<0:n-sub1> : int) : int) in
                      (× (<2:n> : int) (<0:rec-res> : int) : int)
                      : int)
                     : int)
                  : int)
               : (int ⊸ int))
            : ((int ⊸ int) ⊸ (int ⊸ int)))
           : (int ⊸ int))
        in
      (app (<0:factorial> : (int ⊸ int)) (5 : int) : int)
      : int)
     : int)
    -----------unboxed_list[invalid]-----------
    (fun map_int (<> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) :
      (rec [] (⊕ (⊗) (⊗ int [0:α]))) .
      (split (<> : (int ⊸ int)) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
         (<0:p> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) in
       (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
          (cases (unfold (rec [] (⊕ (⊗) (⊗ int [0:α])))
                    (<0:lst> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                    : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
             (case (<> : (⊗))
               (inj 0 (<0:nil> : (⊗))
                  : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
             (case (<> : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))
               (split (<> : int) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
                  (<0:cons> : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))) in
                (inj 1
                   (tup (app (<4:f> : (int ⊸ int)) (<1:hd> : int) : int)
                      (app
                         (coderef map_int
                            : ((⊗ (int ⊸ int)
                                 (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                                ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                         (tup (<4:f> : (int ⊸ int))
                            (<0:tl> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                          : (⊗ (int ⊸ int)
                              (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                         : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                    : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                   : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
               : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
           : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
          : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
      : (rec [] (⊕ (⊗) (⊗ int [0:α])))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
       (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
          (inj 0 (tup : (⊗))
             : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
          : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
       in
     (app
        (coderef map_int
           : ((⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int [0:α])))) ⊸
               (rec [] (⊕ (⊗) (⊗ int [0:α])))))
        (tup
           (λ (<> : int) : int .
              (+ (<0:x> : int) (1 : int) : int)
            : (int ⊸ int))
           (<0:lst> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
         : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
        : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
     : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
    -----------boxed_list-----------
    (fun map_int
      (<> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) :
      (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))) .
      (split (<> : (int ⊸ int))
         (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) =
         (<0:p> : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
         in
       (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
          (cases (unfold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
                    (<0:lst> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                    : (⊕ (⊗)
                        (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
             (case (<> : (⊗))
               (inj 0 (<0:nil> : (⊗))
                  : (⊕ (⊗)
                      (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
             (case (<> : (⊗ int
                           (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
               (split (<> : int)
                  (<> : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) =
                  (<0:cons>
                     : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
                  in
                (inj 1
                   (tup (app (<4:f> : (int ⊸ int)) (<1:hd> : int) : int)
                      (new
                         (app
                            (coderef map_int
                               : ((⊗ (int ⊸ int)
                                    (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                                   ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                            (tup (<4:f> : (int ⊸ int))
                               (free
                                  (<0:tl>
                                     : (ref
                                         (rec []
                                           (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                  : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                             : (⊗ (int ⊸ int)
                                 (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                            : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                         : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                    : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
                   : (⊕ (⊗)
                       (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
               : (⊕ (⊗)
                   (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
           : (⊕ (⊗)
               (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
          : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
      : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) =
       (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
          (inj 1
             (tup (5 : int)
                (new
                   (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
                      (inj 0 (tup : (⊗))
                         : (⊕ (⊗)
                             (⊗ int
                               (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
                      : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                   : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
              : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
             : (⊕ (⊗)
                 (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
          : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
       in
     (app
        (coderef map_int
           : ((⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) ⊸
               (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
        (tup
           (λ (<> : int) : int .
              (+ (<0:x> : int) (1 : int) : int)
            : (int ⊸ int))
           (<0:lst> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
         : (⊗ (int ⊸ int) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
        : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
     : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
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
                                  (inj 0 (tup : (⊗))
                                     : (⊕ (⊗)
                                         (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                                  : (rec [] (⊕ (⊗) (ref [0:a]))))
                               : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                            : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                         : (rec [] (⊕ (⊗) (ref [0:a]))))
                      : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                   : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                : (rec [] (⊕ (⊗) (ref [0:a]))))
             : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
          : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
       : (rec [] (⊕ (⊗) (ref [0:a]))))
    -----------peano-----------
    (fun add
      (<> : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) :
      (rec [] (⊕ (⊗) (ref [0:a]))) .
      (split (<> : (rec [] (⊕ (⊗) (ref [0:a]))))
         (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
         (<0:p>
            : (⊗ (rec [] (⊕ (⊗) (ref [0:a])))
                (rec [] (⊕ (⊗) (ref [0:a])))))
         in
       (cases (unfold (rec [] (⊕ (⊗) (ref [0:a])))
                 (<1:left> : (rec [] (⊕ (⊗) (ref [0:a]))))
                 : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
          (case (<> : (⊗)) (<1:right> : (rec [] (⊕ (⊗) (ref [0:a])))))
          (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
            (fold (rec [] (⊕ (⊗) (ref [0:a])))
               (inj 1
                  (new
                     (app
                        (coderef add
                           : ((⊗ (rec [] (⊕ (⊗) (ref [0:a])))
                                (rec [] (⊕ (⊗) (ref [0:a]))))
                               ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                        (tup
                           (free
                              (<0:succ> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                              : (rec [] (⊕ (⊗) (ref [0:a]))))
                           (<1:right> : (rec [] (⊕ (⊗) (ref [0:a]))))
                         : (⊗ (rec [] (⊕ (⊗) (ref [0:a])))
                             (rec [] (⊕ (⊗) (ref [0:a])))))
                        : (rec [] (⊕ (⊗) (ref [0:a]))))
                     : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                  : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
               : (rec [] (⊕ (⊗) (ref [0:a])))))
        : (rec [] (⊕ (⊗) (ref [0:a]))))
      : (rec [] (⊕ (⊗) (ref [0:a])))))

    (fun from-int (<> : int) : (rec [] (⊕ (⊗) (ref [0:a]))) .
      (fold (rec [] (⊕ (⊗) (ref [0:a])))
         (if0 (<0:int> : int)
          then (inj 0 (tup : (⊗))
                  : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
          else
            (inj 1
               (new
                  (app
                     (coderef from-int : (int ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                     (- (<0:int> : int) (1 : int) : int)
                     : (rec [] (⊕ (⊗) (ref [0:a]))))
                  : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
               : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
          : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
         : (rec [] (⊕ (⊗) (ref [0:a])))))

    (fun to-int (<> : (rec [] (⊕ (⊗) (ref [0:a])))) : int .
      (cases (unfold (rec [] (⊕ (⊗) (ref [0:a])))
                (<0:peano> : (rec [] (⊕ (⊗) (ref [0:a]))))
                : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
         (case (<> : (⊗)) (0 : int))
         (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
           (+ (1 : int)
              (app (coderef to-int : ((rec [] (⊕ (⊗) (ref [0:a]))) ⊸ int))
                 (free (<0:succ> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                    : (rec [] (⊕ (⊗) (ref [0:a]))))
                 : int)
              : int))
       : int))

    (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
       (app (coderef from-int : (int ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
          (6 : int) : (rec [] (⊕ (⊗) (ref [0:a]))))
       in
     (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
        (app (coderef from-int : (int ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
           (7 : int) : (rec [] (⊕ (⊗) (ref [0:a]))))
        in
      (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
         (app
            (coderef add
               : ((⊗ (rec [] (⊕ (⊗) (ref [0:a])))
                    (rec [] (⊕ (⊗) (ref [0:a]))))
                   ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
            (tup (<1:six> : (rec [] (⊕ (⊗) (ref [0:a]))))
               (<0:seven> : (rec [] (⊕ (⊗) (ref [0:a]))))
             : (⊗ (rec [] (⊕ (⊗) (ref [0:a])))
                 (rec [] (⊕ (⊗) (ref [0:a])))))
            : (rec [] (⊕ (⊗) (ref [0:a]))))
         in
       (app (coderef to-int : ((rec [] (⊕ (⊗) (ref [0:a]))) ⊸ int))
          (<0:sum> : (rec [] (⊕ (⊗) (ref [0:a])))) : int)
       : int)
      : int)
     : int)
    -----------mini_zip-----------
    (fun add1 (<> : int) : int .
      (+ (<0:x> : int) (1 : int) : int))

    (export fun typle_add1 (<> : (⊗ int int)) : (⊗ int int) .
      (split (<> : int) (<> : int) = (<0:x> : (⊗ int int)) in
       (tup (app (coderef add1 : (int ⊸ int)) (<1:x1> : int) : int)
          (app (coderef add1 : (int ⊸ int)) (<0:x2> : int) : int)
        : (⊗ int int))
      : (⊗ int int)))

    (fun mini_zip_specialized (<> : (⊗ (ref int) (ref (ref int)))) :
      (ref (⊗ int (ref int))) .
      (split (<> : (ref int)) (<> : (ref (ref int))) =
         (<0:p> : (⊗ (ref int) (ref (ref int)))) in
       (new
          (tup (free (<1:a> : (ref int)) : int)
             (free (<0:b> : (ref (ref int))) : (ref int))
           : (⊗ int (ref int)))
          : (ref (⊗ int (ref int))))
      : (ref (⊗ int (ref int))))) |}]
