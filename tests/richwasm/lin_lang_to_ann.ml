open! Core
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Test_utils
  open Richwasm_lin_lang

  type syntax = Syntax.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let elab x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp

  let syntax_pipeline x =
    x
    |> Main.compile_ast
    |> Main.Res.T.run
    |> fst
    |> or_fail_pp Main.CompileErr.pp
    |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = AnnRichWasm.Module.pp
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {xxx|
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (MonoFunT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))))
        (mf_locals ()) (mf_body ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {xxx|
    (module
      (func
          (->
          (prod (val (prod i32 i32 i32 i32) norefs) (num (val i32 norefs) i32)
            (num (val i32 norefs) i32) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32) (num (val i32 norefs) i32)
                 (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32 i32 i32) norefs) (num (val i32 norefs) i32)
                    (num (val i32 norefs) i32) (num (val i32 norefs) i32)
                    (num (val i32 norefs) i32))])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type
         (MonoFunT ()
          ((ProdT (VALTYPE (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R))) NoRefs)
            ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))))))
        (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 1)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 2)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 3)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 4)
          (IGroup
           (InstrT
            ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))
            ((ProdT (VALTYPE (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R))) NoRefs)
              ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))
               (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))))))))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  run {| (tup (tup 1 (tup 2 3) 4 5) (tup 6 7)) |};
  [%expect
    {xxx|
    (module
      (func
          (->
          (prod (val (prod (prod i32 (prod i32 i32) i32 i32) (prod i32 i32)) norefs)
            (prod (val (prod i32 (prod i32 i32) i32 i32) norefs) (num (val i32 norefs) i32)
              (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
              (num (val i32 norefs) i32) (num (val i32 norefs) i32))
            (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32)
                 (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                 (num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 (prod i32 i32) i32 i32) norefs) (num (val i32 norefs) i32)
                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                    (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        num_const 6 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 7 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        group ;; [(prod (val (prod i32 (prod i32 i32) i32 i32) norefs) (num (val i32 norefs) i32)
                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                    (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                 (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] ->
                 [(prod (val (prod (prod i32 (prod i32 i32) i32 i32) (prod i32 i32)) norefs)
                    (prod (val (prod i32 (prod i32 i32) i32 i32) norefs)
                      (num (val i32 norefs) i32)
                      (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                      (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))])
      (table)
      (export "_start" (func 0))) |xxx}];

  run {| (new 10) |};
  [%expect
    {xxx|
    (module
      (func (-> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        new ;; [(num (val i32 norefs) i32)] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))])
      (table)
      (export "_start" (func 0))) |xxx}];

  run {| (1 + 2) |};
  [%expect
    {xxx|
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (MonoFunT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 1)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))) 2)
          (INum
           (InstrT ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))
            ((NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))))
           (IInt2 I32T AddI)))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  (* [%expect {| |}]; *)
  ()

let%expect_test "examples" =
  output_examples ();
  [%expect
    {xxx|
    -----------one-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------flat_tuple-----------
    (module
      (func
          (->
          (prod (val (prod i32 i32 i32 i32) norefs) (num (val i32 norefs) i32)
            (num (val i32 norefs) i32) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32) (num (val i32 norefs) i32)
                 (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32 i32 i32) norefs) (num (val i32 norefs) i32)
                    (num (val i32 norefs) i32) (num (val i32 norefs) i32)
                    (num (val i32 norefs) i32))])
      (table)
      (export "_start" (func 0)))
    -----------nested_tuple-----------
    (module
      (func
          (->
          (prod (val (prod (prod i32 i32) (prod i32 i32)) norefs)
            (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
            (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        group ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                 (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] ->
                 [(prod (val (prod (prod i32 i32) (prod i32 i32)) norefs)
                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))
                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))])
      (table)
      (export "_start" (func 0)))
    -----------single_sum-----------
    (module
      (func (-> (sum (val (sum (prod)) norefs)  (prod (val (prod) norefs))))
        group ;; [] -> [(prod (val (prod) norefs))]
        inject 0 ;; [(prod (val (prod) norefs))] -> [(sum (val (sum (prod)) norefs)  (prod (val (prod) norefs)))])
      (table)
      (export "_start" (func 0)))
    -----------double_sum-----------
    (module
      (func (-> (sum (val (sum (prod) i32) norefs)  (prod (val (prod) norefs)) (num (val i32 norefs) i32)))
        num_const 15 ;; [] -> [(num (val i32 norefs) i32)]
        inject 1 ;; [(num (val i32 norefs) i32)] ->
                    [(sum (val (sum (prod) i32) norefs)  (prod (val (prod) norefs)) (num (val i32 norefs) i32))])
      (table)
      (export "_start" (func 0)))
    -----------arith_add-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 9 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_sub-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 67 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 41 ;; [] -> [(num (val i32 norefs) i32)]
        i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_mul-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        i32.mul ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_div-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const -30 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        i32.div_s ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------app_ident-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32 (prod) i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                            -> [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod)) norefs) (rep (prod))))
                            (prod (val (prod) norefs))]
        local.set 3 ;; [(prod (val (prod) norefs))] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod)) norefs) (rep (prod))))] -> []
        local.get move 3 ;; [] -> [(prod (val (prod) norefs))]
        ungroup ;; [(prod (val (prod) norefs))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)])
      (table 0)
      (export "_start" (func 1)))
    -----------nested_arith-----------
    (module
      (func (-> (num (val i32 norefs) i32))
        num_const 9 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
        i32.mul ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)])
      (table)
      (export "_start" (func 0)))
    -----------let_bind-----------
    (module
      (func (-> (num (val i32 norefs) i32)) (local i32)
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 0 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 0 ;; [] -> [(num (val i32 norefs) i32)]
        local.get move 0 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (table)
      (export "_start" (func 0)))
    -----------add_one_program-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)])
      (table 0)
      (export "add-one" (func 0))
      (export "_start" (func 1)))
    -----------add_tup_ref-----------
    (module
      (func (-> (num (val i32 norefs) i32)) (local ptr i32 ptr i32 i32)
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        new ;; [(num (val i32 norefs) i32)] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.set 0 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        local.get move 0 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        group ;; [(num (val i32 norefs) i32)
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] ->
                 [(prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
        ungroup ;; [(prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
                   -> [(num (val i32 norefs) i32)
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.set 1 ;; [(num (val i32 norefs) i32)] -> []
        local.get move 2 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] ->
                            [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))
                            (num (val i32 norefs) i32)]
        local.set 3 ;; [(num (val i32 norefs) i32)] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))] -> []
        local.get move 3 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 1 ;; [] -> [(num (val i32 norefs) i32)]
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 0 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> [])
      (table)
      (export "_start" (func 0)))
    -----------print_10-----------
    (module
      (import ((prod (val (prod ptr i32) anyrefs)
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                 (num (val i32 norefs) i32))
              -> (prod (val (prod) norefs))))
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (prod (val (prod) norefs)))
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        call 0 (inst) ;; [(prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                            (num (val i32 norefs) i32))]
                         -> [(prod (val (prod) norefs))])
      (func (-> (prod (val (prod) norefs))) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (prod (val (prod) norefs))))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (prod (val (prod) norefs))))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (prod (val (prod) norefs))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (prod (val (prod) norefs))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (prod (val (prod) norefs))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (prod (val (prod) norefs))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (prod (val (prod) norefs))))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (prod (val (prod) norefs))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (prod (val (prod) norefs))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (prod (val (prod) norefs))))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (prod (val (prod) norefs))))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (prod (val (prod) norefs))))]
                           -> [(prod (val (prod) norefs))]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (prod (val (prod) norefs))))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (prod (val (prod) norefs))))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (prod (val (prod) norefs))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(prod (val (prod) norefs))])
      (table 0)
      (export "_start" (func 1)))
    -----------closure-----------
    (module
      (func
          ((prod (val (prod ptr (prod)) anyrefs)
             (ref (val ptr anyrefs) (base mm)
               (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
             (prod (val (prod) norefs)))
          -> (num (val i32 norefs) i32)) (local ptr (prod) (prod i32) i32
          (prod))
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod)) anyrefs)
                               (ref (val ptr anyrefs) (base mm)
                                 (ser (mem (rep (prod i32)) norefs)
                                   (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                               (prod (val (prod) norefs)))]
        ungroup ;; [(prod (val (prod ptr (prod)) anyrefs)
                      (ref (val ptr anyrefs) (base mm)
                        (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                      (prod (val (prod) norefs)))]
                   ->
                   [(ref (val ptr anyrefs) (base mm)
                      (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                   (prod (val (prod) norefs))]
        local.set 2 ;; [(prod (val (prod) norefs))] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                       -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep (prod i32)) norefs)
                                 (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep (prod i32)) norefs)
                                 (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                            -> [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod i32)) norefs) (rep (prod i32))))
                            (prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        local.set 3 ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod i32)) norefs) (rep (prod i32))))] -> []
        local.get move 3 ;; [] -> [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] -> [(num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 2 ;; [] -> [(prod (val (prod) norefs))]
        local.set 5 ;; [(prod (val (prod) norefs))] -> []
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        local.get move 5 ;; [] -> [(prod (val (prod) norefs))]
        drop ;; [(prod (val (prod) norefs))] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 2 ;; [] -> [(prod (val (prod) norefs))]
        drop ;; [(prod (val (prod) norefs))] -> [])
      (func (-> (num (val i32 norefs) i32)) (local i32 (prod i32 ptr) i32 ptr)
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 0 ;; [(num (val i32 norefs) i32)] -> []
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod)) anyrefs)
                           (ref (val ptr anyrefs) (base mm)
                             (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                           (prod (val (prod) norefs)))
                        -> (num (val i32 norefs) i32)))]
        local.get copy 0 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32)] -> [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        new ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (prod)) anyrefs)
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                       (prod (val (prod) norefs)))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm)
                   (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                 ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod)) anyrefs)
                         (ref (val ptr anyrefs) (base mm)
                           (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                         (prod (val (prod) norefs)))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm)
                      (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod)) anyrefs)
                        (ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                        (prod (val (prod) norefs)))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod i32) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                          (prod (val (prod) norefs)))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))))]
        unpack (localfx [0 => (num (val i32 norefs) i32)] [1 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [2 => (plug (val (prod i32) norefs) (prod i32))] [3 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod)) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                 (prod (val (prod) norefs)))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod)) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                      (prod (val (prod) norefs)))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                             (prod (val (prod) norefs)))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                           (prod (val (prod) norefs)))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))]
          local.set 3 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))] -> []
          local.set 2 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                               (prod (val (prod) norefs)))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 3 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))]
          group ;; [] -> [(prod (val (prod) norefs))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                   (prod (val (prod) norefs))] ->
                   [(prod (val (prod ptr (prod)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                      (prod (val (prod) norefs)))]
          local.get copy 2 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                    (prod (val (prod) norefs)))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr (prod)) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                              (prod (val (prod) norefs)))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (prod)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                (prod (val (prod) norefs)))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 2 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                    (prod (val (prod) norefs)))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                        (prod (val (prod) norefs)))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 3 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 1 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod i32) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                         (prod (val (prod) norefs)))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 0 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (table 0)
      (export "_start" (func 1)))
    -----------closure_call_var-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm)
               (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32 (prod i32) i32 i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm)
                                 (ser (mem (rep (prod i32)) norefs)
                                   (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm)
                        (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                      (num (val i32 norefs) i32))]
                   ->
                   [(ref (val ptr anyrefs) (base mm)
                      (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                       -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep (prod i32)) norefs)
                                 (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep (prod i32)) norefs)
                                 (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                            -> [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod i32)) norefs) (rep (prod i32))))
                            (prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        local.set 3 ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep (prod i32)) norefs) (rep (prod i32))))] -> []
        local.get move 3 ;; [] -> [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] -> [(num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 5 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 5 ;; [] -> [(num (val i32 norefs) i32)]
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 5 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func (-> (num (val i32 norefs) i32)) (local i32 i32 (prod i32 ptr) i32 ptr)
        num_const 21 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 0 ;; [(num (val i32 norefs) i32)] -> []
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        local.set 1 ;; [(num (val i32 norefs) i32)] -> []
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm)
                             (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        local.get copy 1 ;; [] -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32)] -> [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))]
        new ;; [(prod (val (prod i32) norefs) (num (val i32 norefs) i32))] ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm)
                   (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))]
                 ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm)
                           (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm)
                      (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (prod i32)) norefs) (prod (val (prod i32) norefs) (num (val i32 norefs) i32)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod i32) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))))]
        unpack (localfx [0 => (num (val i32 norefs) i32)] [1 => (num (val i32 norefs) i32)]
                 [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 2 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
                         -> []
          local.get move 2 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))]
          local.set 4 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))] -> []
          local.set 3 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 4 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))]
          local.get copy 0 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 3 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 3 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 4 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod i32) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod i32)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 0 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (table 0)
      (export "_start" (func 1)))
    -----------triangle_tl-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32 (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eqz ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if
          (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (num (val i32 norefs) i32)] [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))])
          num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
        else
          local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
          coderef 0 ;; [] ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))]
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          group ;; [(coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                   [(prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
          pack ;; [(prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                     (prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (num (val i32 norefs) i32))
                         -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
          unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                   [2 => (num (val i32 norefs) i32)] [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))])
            local.set 3 ;; [(prod (val (prod i32 ptr) anyrefs)
                              (coderef (val i32 norefs)
                                ((prod (val (prod ptr i32) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (num (val i32 norefs) i32))
                                -> (num (val i32 norefs) i32)))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                           -> []
            local.get move 3 ;; [] ->
                                [(prod (val (prod i32 ptr) anyrefs)
                                   (coderef (val i32 norefs)
                                     ((prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (num (val i32 norefs) i32))
                                     -> (num (val i32 norefs) i32)))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
            ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                          (coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                       ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.set 5 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
            local.set 4 ;; [(coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))]
                           -> []
            local.get move 5 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
            num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
            i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
            group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                     (num (val i32 norefs) i32)] ->
                     [(prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))]
            local.get copy 4 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))]
            call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             (coderef (val i32 norefs)
                               ((prod (val (prod ptr i32) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (num (val i32 norefs) i32))
                               -> (num (val i32 norefs) i32)))]
                             -> [(num (val i32 norefs) i32)]
            local.get move 4 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))]
            drop ;; [(coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))]
                    -> []
            local.get move 5 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
            drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                    (prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                 -> [(num (val i32 norefs) i32)]
          i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        end ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)])
      (table 0)
      (export "_start" (func 1)))
    -----------factorial_tl-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32 i32 (prod i32 ptr) i32 ptr i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eqz ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if
          (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (num (val i32 norefs) i32)] [3 => (plug (val (prod i32) norefs) (prod i32))]
            [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))] [5 => (plug (val (prod i32) norefs) (prod i32))]
            [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))])
          num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        else
          local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
          num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
          i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
          local.set 3 ;; [(num (val i32 norefs) i32)] -> []
          coderef 0 ;; [] ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))]
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          group ;; [(coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                   [(prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
          pack ;; [(prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                     (prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (num (val i32 norefs) i32))
                         -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
          unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                   [2 => (num (val i32 norefs) i32)] [3 => (num (val i32 norefs) i32)]
                   [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                   [7 => (plug (val (prod i32) norefs) (prod i32))])
            local.set 4 ;; [(prod (val (prod i32 ptr) anyrefs)
                              (coderef (val i32 norefs)
                                ((prod (val (prod ptr i32) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (num (val i32 norefs) i32))
                                -> (num (val i32 norefs) i32)))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                           -> []
            local.get move 4 ;; [] ->
                                [(prod (val (prod i32 ptr) anyrefs)
                                   (coderef (val i32 norefs)
                                     ((prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (num (val i32 norefs) i32))
                                     -> (num (val i32 norefs) i32)))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
            ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                          (coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                       ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.set 6 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
            local.set 5 ;; [(coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))]
                           -> []
            local.get move 6 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.get copy 3 ;; [] -> [(num (val i32 norefs) i32)]
            group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                     (num (val i32 norefs) i32)] ->
                     [(prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))]
            local.get copy 5 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))]
            call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             (coderef (val i32 norefs)
                               ((prod (val (prod ptr i32) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (num (val i32 norefs) i32))
                               -> (num (val i32 norefs) i32)))]
                             -> [(num (val i32 norefs) i32)]
            local.get move 5 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))]
            drop ;; [(coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))]
                    -> []
            local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
            local.get move 4 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
            drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                    (prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                 -> [(num (val i32 norefs) i32)]
          local.set 7 ;; [(num (val i32 norefs) i32)] -> []
          local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
          local.get copy 7 ;; [] -> [(num (val i32 norefs) i32)]
          i32.mul ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
          local.get move 7 ;; [] -> [(num (val i32 norefs) i32)]
          drop ;; [(num (val i32 norefs) i32)] -> []
          local.get move 3 ;; [] -> [(num (val i32 norefs) i32)]
          drop ;; [(num (val i32 norefs) i32)] -> []
        end ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)])
      (table 0)
      (export "factorial" (func 0))
      (export "_start" (func 1)))
    -----------safe_div-----------
    (module
      (func
          ((prod (val (prod ptr (prod i32 i32)) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
          -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))) (local ptr
          (prod i32 i32) i32 i32 i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))]
        ungroup ;; [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        local.set 2 ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] ->
                            [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] ->
                   [(num (val i32 norefs) i32) (num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.set 3 ;; [(num (val i32 norefs) i32)] -> []
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eqz ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if
          (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
            [3 => (num (val i32 norefs) i32)] [4 => (num (val i32 norefs) i32)]
            [5 => (plug (val (prod i32) norefs) (prod i32))])
          group ;; [] -> [(prod (val (prod) norefs))]
          inject 1 ;; [(prod (val (prod) norefs))] ->
                      [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        else
          local.get copy 3 ;; [] -> [(num (val i32 norefs) i32)]
          local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
          i32.div_s ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
          local.set 5 ;; [(num (val i32 norefs) i32)] -> []
          local.get copy 5 ;; [] -> [(num (val i32 norefs) i32)]
          inject 0 ;; [(num (val i32 norefs) i32)] ->
                      [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
          local.get move 5 ;; [] -> [(num (val i32 norefs) i32)]
          drop ;; [(num (val i32 norefs) i32)] -> []
        end ;; [(num (val i32 norefs) i32)] ->
               [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        local.get move 3 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        drop ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] -> [])
      (func
          ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
          -> (num (val i32 norefs) i32)) (local ptr (sum i32 (prod)) i32
          (prod))
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (sum i32 (prod))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))]
        ungroup ;; [(prod (val (prod ptr (sum i32 (prod))) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        local.set 2 ;; [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] ->
                            [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        case
          (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
            [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod) norefs) (prod))])
          (0
            local.set 3 ;; [(num (val i32 norefs) i32)] -> []
            local.get copy 3 ;; [] -> [(num (val i32 norefs) i32)]
            local.get move 3 ;; [] -> [(num (val i32 norefs) i32)]
            drop ;; [(num (val i32 norefs) i32)] -> [])
          (1
            local.set 4 ;; [(prod (val (prod) norefs))] -> []
            num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
            local.get move 4 ;; [] -> [(prod (val (prod) norefs))]
            drop ;; [(prod (val (prod) norefs))] -> [])
        end ;; [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] ->
               [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        drop ;; [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr (sum i32 (prod)) (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                        -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                    -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                      -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                     -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                       -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                              ->
                              (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32)
                                        (num (val i32 norefs) i32)))
                                   ->
                                   (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32)
                                     (prod (val (prod) norefs)))))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                          -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                        -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                            -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
          num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                   [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] ->
                   [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32)
                                      (num (val i32 norefs) i32)))
                                 ->
                                 (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
          call_indirect ;; [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                             -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
                           -> [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32)
                                      (num (val i32 norefs) i32)))
                                 ->
                                 (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                     -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod i32 i32)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
                      -> (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        local.set 3 ;; [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] -> []
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 4 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 4 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (sum (val (sum i32 (prod)) norefs)
                                        (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 6 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 6 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get copy 3 ;; [] ->
                              [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] ->
                   [(prod (val (prod ptr (sum i32 (prod))) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))]
          local.get copy 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32)
                                      (prod (val (prod) norefs))))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr (sum i32 (prod))) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32)
                                      (prod (val (prod) norefs))))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 4 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (sum i32 (prod))) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs))))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 3 ;; [] ->
                            [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))]
        drop ;; [(sum (val (sum i32 (prod)) norefs)  (num (val i32 norefs) i32) (prod (val (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 2)))
    -----------incr_n-----------
    (module
      (func
          ((prod (val (prod ptr ptr) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
          -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))) (local ptr ptr ptr
          i32 ptr i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr ptr) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
        ungroup ;; [(prod (val (prod ptr ptr) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
        swap (path) ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                       (num (val i32 norefs) i32)] ->
                       [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                       (num (val i32 norefs) i32)]
        group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                 (num (val i32 norefs) i32)] ->
                 [(prod (val (prod ptr i32) anyrefs)
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                    (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                   (num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.set 3 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.get move 3 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        swap (path) ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                       (num (val i32 norefs) i32)] ->
                       [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                       (num (val i32 norefs) i32)]
        group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                 (num (val i32 norefs) i32)] ->
                 [(prod (val (prod ptr i32) anyrefs)
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                    (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                   (num (val i32 norefs) i32)]
        local.set 6 ;; [(num (val i32 norefs) i32)] -> []
        local.set 5 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.get move 5 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.get move 5 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 6 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 3 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> [])
      (func
          ((prod (val (prod ptr (prod ptr i32)) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (prod (val (prod ptr i32) anyrefs)
               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
               (num (val i32 norefs) i32)))
          -> (num (val i32 norefs) i32)) (local ptr (prod ptr i32) ptr i32 i32
          (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                 (num (val i32 norefs) i32)))]
        ungroup ;; [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                        (num (val i32 norefs) i32)))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (prod (val (prod ptr i32) anyrefs)
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                     (num (val i32 norefs) i32))]
        local.set 2 ;; [(prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                          (num (val i32 norefs) i32))]
                       -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                   (num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.set 3 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eqz ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if
          (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))] [3 => (plug (val (prod i32) norefs) (prod i32))]
            [4 => (num (val i32 norefs) i32)] [5 => (plug (val (prod i32) norefs) (prod i32))]
            [6 => (plug (val (prod i32 i32) norefs) (prod i32 i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
            [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [10 => (plug (val (prod i32) norefs) (prod i32))] [11 => (plug (val (prod i32) norefs) (prod i32))])
          local.get move 3 ;; [] ->
                              [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
          load (path) move ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
                              -> [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))
                              (num (val i32 norefs) i32)]
          local.set 5 ;; [(num (val i32 norefs) i32)] -> []
          drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))] -> []
          local.get move 5 ;; [] -> [(num (val i32 norefs) i32)]
        else
          coderef 1 ;; [] ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                               (num (val i32 norefs) i32)))
                          -> (num (val i32 norefs) i32)))]
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          group ;; [(coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                           (num (val i32 norefs) i32)))
                      -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                   [(prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                             (num (val i32 norefs) i32)))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
          pack ;; [(prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                          (prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                            (num (val i32 norefs) i32)))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                     (prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                              (num (val i32 norefs) i32)))
                         -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
          unpack (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
                   [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                   [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (num (val i32 norefs) i32)]
                   [5 => (plug (val (prod i32) norefs) (prod i32))]
                   [6 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [7 => (plug (val (prod i32) norefs) (prod i32))] [8 => (plug (val (prod i32) norefs) (prod i32))]
                   [9 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [10 => (plug (val (prod i32) norefs) (prod i32))] [11 => (plug (val (prod i32) norefs) (prod i32))])
            local.set 6 ;; [(prod (val (prod i32 ptr) anyrefs)
                              (coderef (val i32 norefs)
                                ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (prod (val (prod ptr i32) anyrefs)
                                     (ref (val ptr anyrefs) (base mm)
                                       (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                     (num (val i32 norefs) i32)))
                                -> (num (val i32 norefs) i32)))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                           -> []
            local.get move 6 ;; [] ->
                                [(prod (val (prod i32 ptr) anyrefs)
                                   (coderef (val i32 norefs)
                                     ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (prod (val (prod ptr i32) anyrefs)
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                          (num (val i32 norefs) i32)))
                                     -> (num (val i32 norefs) i32)))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
            ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                          (coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                 (num (val i32 norefs) i32)))
                            -> (num (val i32 norefs) i32)))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                       ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                               (num (val i32 norefs) i32)))
                          -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.set 8 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
            local.set 7 ;; [(coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (prod (val (prod ptr i32) anyrefs)
                                   (ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                   (num (val i32 norefs) i32)))
                              -> (num (val i32 norefs) i32)))]
                           -> []
            local.get move 8 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            coderef 0 ;; [] ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr ptr) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                            -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
            group ;; [] -> [(prod (val (prod) norefs))]
            new ;; [(prod (val (prod) norefs))] ->
                   [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            group ;; [(coderef (val i32 norefs)
                        ((prod (val (prod ptr ptr) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                        -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                     [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr ptr) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                          -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
            pack ;; [(prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr ptr) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                         -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                       (prod (val (prod i32 ptr) anyrefs)
                         (coderef (val i32 norefs)
                           ((prod (val (prod ptr ptr) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                           -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
            unpack (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
                     [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                     [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (num (val i32 norefs) i32)]
                     [5 => (plug (val (prod i32) norefs) (prod i32))]
                     [6 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [7 =>
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                            (num (val i32 norefs) i32)))
                       -> (num (val i32 norefs) i32)))]
                     [8 => (plug (val (prod i32) norefs) (prod i32))]
                     [9 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [10 => (plug (val (prod i32) norefs) (prod i32))] [11 => (plug (val (prod i32) norefs) (prod i32))])
              local.set 9 ;; [(prod (val (prod i32 ptr) anyrefs)
                                (coderef (val i32 norefs)
                                  ((prod (val (prod ptr ptr) anyrefs)
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                     (ref (val ptr anyrefs) (base mm)
                                       (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                  ->
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                             -> []
              local.get move 9 ;; [] ->
                                  [(prod (val (prod i32 ptr) anyrefs)
                                     (coderef (val i32 norefs)
                                       ((prod (val (prod ptr ptr) anyrefs)
                                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                       ->
                                       (ref (val ptr anyrefs) (base mm)
                                         (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
              ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr ptr) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                              -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr ptr) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                            -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.set 11 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
              local.set 10 ;; [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr ptr) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (ref (val ptr anyrefs) (base mm)
                                      (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                 ->
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
                              -> []
              local.get move 11 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.get move 3 ;; [] ->
                                  [(ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
              group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] ->
                       [(prod (val (prod ptr ptr) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
              local.get copy 10 ;; [] ->
                                   [(coderef (val i32 norefs)
                                      ((prod (val (prod ptr ptr) anyrefs)
                                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                      ->
                                      (ref (val ptr anyrefs) (base mm)
                                        (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
              call_indirect ;; [(prod (val (prod ptr ptr) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                               (coderef (val i32 norefs)
                                 ((prod (val (prod ptr ptr) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (ref (val ptr anyrefs) (base mm)
                                      (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                 ->
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
                               ->
                               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
              local.get move 10 ;; [] ->
                                   [(coderef (val i32 norefs)
                                      ((prod (val (prod ptr ptr) anyrefs)
                                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                                      ->
                                      (ref (val ptr anyrefs) (base mm)
                                        (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
              drop ;; [(coderef (val i32 norefs)
                         ((prod (val (prod ptr ptr) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                         -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
                      -> []
              local.get move 11 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
              drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
              local.get move 9 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
              drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                      (prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr ptr) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))
                          -> (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
            local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
            num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
            i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
            group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                     (num (val i32 norefs) i32)] ->
                     [(prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                        (num (val i32 norefs) i32))]
            group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                     (prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                       (num (val i32 norefs) i32))]
                     ->
                     [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                          (num (val i32 norefs) i32)))]
            local.get copy 7 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                        (num (val i32 norefs) i32)))
                                   -> (num (val i32 norefs) i32)))]
            call_indirect ;; [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (prod (val (prod ptr i32) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                  (num (val i32 norefs) i32)))
                             (coderef (val i32 norefs)
                               ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm)
                                      (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                    (num (val i32 norefs) i32)))
                               -> (num (val i32 norefs) i32)))]
                             -> [(num (val i32 norefs) i32)]
            local.get move 7 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                        (num (val i32 norefs) i32)))
                                   -> (num (val i32 norefs) i32)))]
            drop ;; [(coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                            (num (val i32 norefs) i32)))
                       -> (num (val i32 norefs) i32)))]
                    -> []
            local.get move 8 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
            local.get move 6 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
            drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                    (prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                             (num (val i32 norefs) i32)))
                        -> (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                 -> [(num (val i32 norefs) i32)]
        end ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 3 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> [])
      (func (-> (num (val i32 norefs) i32)) (local ptr (prod i32 ptr) i32 ptr)
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        new ;; [(num (val i32 norefs) i32)] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.set 0 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                             (num (val i32 norefs) i32)))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                         (num (val i32 norefs) i32)))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                           (num (val i32 norefs) i32)))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                          (num (val i32 norefs) i32)))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                            (num (val i32 norefs) i32)))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32) norefs) (prod i32))]
                 [1 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [2 => (plug (val (prod i32) norefs) (prod i32))] [3 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (prod (val (prod ptr i32) anyrefs)
                                   (ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                   (num (val i32 norefs) i32)))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                        (num (val i32 norefs) i32)))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                               (num (val i32 norefs) i32)))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                             (num (val i32 norefs) i32)))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 3 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 2 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                 (num (val i32 norefs) i32)))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 3 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get move 0 ;; [] ->
                              [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
          num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                      (num (val i32 norefs) i32))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (prod (val (prod ptr i32) anyrefs)
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                     (num (val i32 norefs) i32))]
                   ->
                   [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                        (num (val i32 norefs) i32)))]
          local.get copy 2 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm)
                                        (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                      (num (val i32 norefs) i32)))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr (prod ptr i32)) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                (num (val i32 norefs) i32)))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (prod (val (prod ptr i32) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                  (num (val i32 norefs) i32)))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 2 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm)
                                        (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                      (num (val i32 norefs) i32)))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                          (num (val i32 norefs) i32)))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 3 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 1 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod ptr i32)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                           (num (val i32 norefs) i32)))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 0 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> [])
      (table 0 1)
      (export "incr_n" (func 1))
      (export "_start" (func 2)))
    -----------fix_factorial[invalid]-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (ExpectedEqStack
         (Fold0
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType ()
               ((Prod
                 ((Ref (Base MM) (Ser (Var 0)))
                  (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                   (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0))))))
          (Plug (Prod ((Atom I32) (Atom I32)))))))
       (instr
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0)))))))))
       (env
        ((local_offset 1)
         (kinds ((VALTYPE (Prod ((Prod ((Atom I32) (Atom Ptr))))) AnyRefs)))
         (labels
          (((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
             (Prod
              ((CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))
               (Ref (Base MM) (Ser (Var 0)))))))))
         (return
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Ref (Base MM) (Ser (Var 0)))
                           (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod
                                  ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Ref (Base MM) (Ser (Var 0)))))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                       (Prod
                        ((CodeRef
                          (FunctionType ()
                           ((Prod
                             ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Ref (Base MM) (Ser (Var 0)))))))))
                   (Ref (Base MM) (Ser (Var 0))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Ref (Base MM) (Ser (Var 0)))
                           (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod
                                  ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Ref (Base MM) (Ser (Var 0)))))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                       (Prod
                        ((CodeRef
                          (FunctionType ()
                           ((Prod
                             ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Ref (Base MM) (Ser (Var 0)))))))))
                   (Ref (Base MM) (Ser (Var 0))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ())) (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32))))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                 (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))
                 (Ref (Base MM) (Ser (Var 0)))))))))
           (Plug (Prod ((Atom I32))))))
         (stack
          ((Plug (Prod ((Atom I32) (Atom I32)))) (Ref (Base MM) (Ser (Var 0)))))))))
     (instr
      (Unpack
       (ValType
        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))))
       InferFx
       ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
        (LocalGet 8 Follow) (LocalGet 5 Follow)
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0))))))))
        (Group 2) (LocalGet 7 Follow) CallIndirect (LocalGet 7 Move) Drop
        (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
              (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                     (Prod
                      ((CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Ref (Base MM) (Ser (Var 0)))))))))
                 (Ref (Base MM) (Ser (Var 0))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0)))))))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
              (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                     (Prod
                      ((CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Ref (Base MM) (Ser (Var 0)))))))))
                 (Ref (Base MM) (Ser (Var 0))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0)))))))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ())) (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists (Type (VALTYPE (Prod ((Prod ((Atom I32) (Atom Ptr))))) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                  (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                   (Prod
                    ((CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                       ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                         (Prod
                          ((CodeRef
                            (FunctionType ()
                             ((Prod
                               ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                             ((Num (Int I32)))))
                           (Ref (Base MM) (Ser (Var 0)))))))))
                     (Ref (Base MM) (Ser (Var 0))))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            (Ref (Base MM) (Ser (Var 0)))))))))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Case
        (1 3
         ((Plug
           (Prod
            ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Ref (Base MM) (Ser (Prod ())))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))))
         ((Plug
           (Prod
            ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Ref (Base MM) (Ser (Prod ())))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))
             (Ref (Base MM) (Ser (Var 0))))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))))))))
     (instr
      (Case
       (ValType
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))))
       InferFx
       (((LocalSet 5) (LocalGet 5 Follow)
         (Inject 0
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 5 Move) Drop)
        ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
         (LocalGet 3 Follow)
         (Unpack (ValType ((Num (Int I32)))) InferFx
          ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
           (LocalGet 11 Follow) (LocalGet 7 Follow) (Group 2)
           (LocalGet 10 Follow) CallIndirect (LocalGet 10 Move) Drop
           (LocalGet 11 Move) Drop (LocalGet 9 Move) Drop))
         (CodeRef 1) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))
                   (Rec
                    (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                     AnyRefs)
                    (Sum
                     ((Prod ())
                      (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
              ((Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Unpack
          (ValType
           ((Rec
             (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
             (Sum
              ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
          InferFx
          ((LocalSet 12) (LocalGet 12 Follow) Ungroup (LocalSet 14) (LocalSet 13)
           (LocalGet 14 Follow) (LocalGet 3 Follow) (LocalGet 8 Follow)
           (Load (Path ()) Move) (LocalSet 15) Drop (LocalGet 15 Move) (Group 2)
           (Group 2) (LocalGet 13 Follow) CallIndirect (LocalGet 13 Move) Drop
           (LocalGet 14 Move) Drop (LocalGet 12 Move) Drop))
         (New MM) (Group 2)
         (Inject 1
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 7 Move) Drop (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
          (Sum
           ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
         (FunctionType () ()
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug
          (Prod
           ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
       (stack
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))))))))
    -----------peano_3-----------
    (module
      (func
          (->
          (rec (val (sum (prod) ptr) anyrefs)
            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
        group ;; [] -> [(prod (val (prod) norefs))]
        inject 0 ;; [(prod (val (prod) norefs))] ->
                    [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                ->
                [(rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
               ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (sum (prod) ptr)) anyrefs)
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        inject 1 ;; [(ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                    ->
                    [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                ->
                [(rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
               ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (sum (prod) ptr)) anyrefs)
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        inject 1 ;; [(ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                    ->
                    [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                ->
                [(rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
               ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (sum (prod) ptr)) anyrefs)
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        inject 1 ;; [(ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                    ->
                    [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                ->
                [(rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))])
      (table)
      (export "_start" (func 0)))
    -----------peano-----------
    (module
      (func
          ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
               (rec (val (sum (prod) ptr) anyrefs)
                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
               (rec (val (sum (prod) ptr) anyrefs)
                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
          ->
          (rec (val (sum (prod) ptr) anyrefs)
            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
          (local ptr (prod (sum (prod) ptr) (sum (prod) ptr)) (sum (prod) ptr)
          (sum (prod) ptr) (prod) ptr (prod i32 ptr) i32 ptr (sum (prod) ptr))
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        ungroup ;; [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
        local.set 2 ;; [(prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
                       -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
        ungroup ;; [(prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
                   ->
                   [(rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                   (rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.set 4 ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       -> []
        local.set 3 ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       -> []
        local.get move 3 ;; [] ->
                            [(rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        unfold ;; [(rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                  ->
                  [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        case
          (localfx [0 => (plug (val (prod i32 i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (plug (val (prod i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32))]
            [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))] [5 => (plug (val (prod) norefs) (prod))]
            [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32) norefs) (prod i32))]
            [10 => (plug (val (prod i32 i32) norefs) (prod i32 i32))])
          (0
            local.set 5 ;; [(prod (val (prod) norefs))] -> []
            local.get move 4 ;; [] ->
                                [(rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
            local.get move 5 ;; [] -> [(prod (val (prod) norefs))]
            drop ;; [(prod (val (prod) norefs))] -> [])
          (1
            local.set 6 ;; [(ref (val ptr anyrefs) (base mm)
                              (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           -> []
            coderef 0 ;; [] ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
            group ;; [] -> [(prod (val (prod) norefs))]
            new ;; [(prod (val (prod) norefs))] ->
                   [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            group ;; [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                     [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
            pack ;; [(prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                            (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                         ->
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                       (prod (val (prod i32 ptr) anyrefs)
                         (coderef (val i32 norefs)
                           ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                           ->
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
            unpack (localfx [0 => (plug (val (prod i32 i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32 i32))]
                     [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                     [2 => (plug (val (prod i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32))]
                     [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [5 => (plug (val (prod) norefs) (prod))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                     [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32) norefs) (prod i32))]
                     [10 => (plug (val (prod i32 i32) norefs) (prod i32 i32))])
              local.set 7 ;; [(prod (val (prod i32 ptr) anyrefs)
                                (coderef (val i32 norefs)
                                  ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                     (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                  ->
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                             -> []
              local.get move 7 ;; [] ->
                                  [(prod (val (prod i32 ptr) anyrefs)
                                     (coderef (val i32 norefs)
                                       ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                          (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                            (rec (val (sum (prod) ptr) anyrefs)
                                              (sum (val (sum (prod) ptr) anyrefs)
                                                (prod (val (prod) norefs))
                                                (ref (val ptr anyrefs) (base mm)
                                                  (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                            (rec (val (sum (prod) ptr) anyrefs)
                                              (sum (val (sum (prod) ptr) anyrefs)
                                                (prod (val (prod) norefs))
                                                (ref (val ptr anyrefs) (base mm)
                                                  (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                       ->
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
              ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                              ->
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.set 9 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
              local.set 8 ;; [(coderef (val i32 norefs)
                                ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                ->
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                             -> []
              local.get move 9 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.get move 6 ;; [] ->
                                  [(ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
              load (path) move ;; [(ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                                  ->
                                  [(ref (val ptr anyrefs) (base mm)
                                     (span (mem (rep (sum (prod) ptr)) norefs) (rep (sum (prod) ptr))))
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              local.set 10 ;; [(rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                              -> []
              drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep (sum (prod) ptr)) norefs) (rep (sum (prod) ptr))))]
                      -> []
              local.get move 10 ;; [] ->
                                   [(rec (val (sum (prod) ptr) anyrefs)
                                      (sum (val (sum (prod) ptr) anyrefs)
                                        (prod (val (prod) norefs))
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              local.get move 4 ;; [] ->
                                  [(rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              group ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       ->
                       [(prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
              group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                       (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
                       ->
                       [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
              local.get copy 8 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum (val (sum (prod) ptr) anyrefs)
                                              (prod (val (prod) norefs))
                                              (ref (val ptr anyrefs) (base mm)
                                                (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum (val (sum (prod) ptr) anyrefs)
                                              (prod (val (prod) norefs))
                                              (ref (val ptr anyrefs) (base mm)
                                                (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                     ->
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
              call_indirect ;; [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                    (rec (val (sum (prod) ptr) anyrefs)
                                      (sum (val (sum (prod) ptr) anyrefs)
                                        (prod (val (prod) norefs))
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                    (rec (val (sum (prod) ptr) anyrefs)
                                      (sum (val (sum (prod) ptr) anyrefs)
                                        (prod (val (prod) norefs))
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                               (coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                               ->
                               [(rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              local.get move 8 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum (val (sum (prod) ptr) anyrefs)
                                              (prod (val (prod) norefs))
                                              (ref (val ptr anyrefs) (base mm)
                                                (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum (val (sum (prod) ptr) anyrefs)
                                              (prod (val (prod) norefs))
                                              (ref (val ptr anyrefs) (base mm)
                                                (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                     ->
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
              drop ;; [(coderef (val i32 norefs)
                         ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                         ->
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                      -> []
              local.get move 9 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
              drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
              local.get move 7 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
              drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                      (prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                   ->
                   [(rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
            new ;; [(rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                   ->
                   [(ref (val ptr anyrefs) (base mm)
                      (ser (mem (rep (sum (prod) ptr)) anyrefs)
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
            inject 1 ;; [(ref (val ptr anyrefs) (base mm)
                           (ser (mem (rep (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                        ->
                        [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm)
                             (ser (mem (rep (sum (prod) ptr)) anyrefs)
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
            fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                    ->
                    [(rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
            local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> [])
        end ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                  (ref (val ptr anyrefs) (base mm)
                    (ser (mem (rep (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
               ->
               [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.get move 3 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        local.get move 4 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32))]
        drop ;; [(plug (val (prod i32 i32 i32 i32) norefs) (prod i32 i32 i32 i32))] -> [])
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          ->
          (rec (val (sum (prod) ptr) anyrefs)
            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
          (local ptr i32 (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eqz ;; [(num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if
          (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (num (val i32 norefs) i32)] [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))])
          group ;; [] -> [(prod (val (prod) norefs))]
          inject 0 ;; [(prod (val (prod) norefs))] ->
                      [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm)
                           (ser (mem (rep (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        else
          coderef 1 ;; [] ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (num (val i32 norefs) i32))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          group ;; [(coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                   [(prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
          pack ;; [(prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                          (num (val i32 norefs) i32))
                       ->
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                     (prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr i32) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (num (val i32 norefs) i32))
                         ->
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
          unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                   [2 => (num (val i32 norefs) i32)] [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                   [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))])
            local.set 3 ;; [(prod (val (prod i32 ptr) anyrefs)
                              (coderef (val i32 norefs)
                                ((prod (val (prod ptr i32) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (num (val i32 norefs) i32))
                                ->
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                           -> []
            local.get move 3 ;; [] ->
                                [(prod (val (prod i32 ptr) anyrefs)
                                   (coderef (val i32 norefs)
                                     ((prod (val (prod ptr i32) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (num (val i32 norefs) i32))
                                     ->
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
            ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                          (coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                       ->
                       [(coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.set 5 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
            local.set 4 ;; [(coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              ->
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           -> []
            local.get move 5 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
            local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
            num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
            i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
            group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                     (num (val i32 norefs) i32)] ->
                     [(prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))]
            local.get copy 4 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   ->
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
            call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             (coderef (val i32 norefs)
                               ((prod (val (prod ptr i32) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (num (val i32 norefs) i32))
                               ->
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                             ->
                             [(rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
            local.get move 4 ;; [] ->
                                [(coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   ->
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
            drop ;; [(coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       ->
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                    -> []
            local.get move 5 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
            drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                    (prod (val (prod i32 ptr) anyrefs)
                      (coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                 ->
                 [(rec (val (sum (prod) ptr) anyrefs)
                    (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          new ;; [(rec (val (sum (prod) ptr) anyrefs)
                    (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                 ->
                 [(ref (val ptr anyrefs) (base mm)
                    (ser (mem (rep (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          inject 1 ;; [(ref (val ptr anyrefs) (base mm)
                         (ser (mem (rep (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                      ->
                      [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm)
                           (ser (mem (rep (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        end ;; [(num (val i32 norefs) i32)] ->
               [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                  (ref (val ptr anyrefs) (base mm)
                    (ser (mem (rep (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        fold ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
                ->
                [(rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func
          ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (rec (val (sum (prod) ptr) anyrefs)
               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
          -> (num (val i32 norefs) i32)) (local ptr (sum (prod) ptr) (prod) ptr
          (prod i32 ptr) i32 ptr (sum (prod) ptr))
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
        ungroup ;; [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.set 2 ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        unfold ;; [(rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                  ->
                  [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
        case
          (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
            [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))] [3 => (plug (val (prod) norefs) (prod))]
            [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
            [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
            [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))])
          (0
            local.set 3 ;; [(prod (val (prod) norefs))] -> []
            num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
            local.get move 3 ;; [] -> [(prod (val (prod) norefs))]
            drop ;; [(prod (val (prod) norefs))] -> [])
          (1
            local.set 4 ;; [(ref (val ptr anyrefs) (base mm)
                              (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           -> []
            num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
            coderef 2 ;; [] ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                            -> (num (val i32 norefs) i32)))]
            group ;; [] -> [(prod (val (prod) norefs))]
            new ;; [(prod (val (prod) norefs))] ->
                   [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            group ;; [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                     [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
            pack ;; [(prod (val (prod i32 ptr) anyrefs)
                       (coderef (val i32 norefs)
                         ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                         -> (num (val i32 norefs) i32)))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                       (prod (val (prod i32 ptr) anyrefs)
                         (coderef (val i32 norefs)
                           ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                           -> (num (val i32 norefs) i32)))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
            unpack (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
                     [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                     [2 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [3 => (plug (val (prod) norefs) (prod))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                     [5 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                     [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                     [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))])
              local.set 5 ;; [(prod (val (prod i32 ptr) anyrefs)
                                (coderef (val i32 norefs)
                                  ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                  -> (num (val i32 norefs) i32)))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                             -> []
              local.get move 5 ;; [] ->
                                  [(prod (val (prod i32 ptr) anyrefs)
                                     (coderef (val i32 norefs)
                                       ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum (val (sum (prod) ptr) anyrefs)
                                              (prod (val (prod) norefs))
                                              (ref (val ptr anyrefs) (base mm)
                                                (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                       -> (num (val i32 norefs) i32)))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
              ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         ->
                         [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                            -> (num (val i32 norefs) i32)))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.set 7 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
              local.set 6 ;; [(coderef (val i32 norefs)
                                ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                -> (num (val i32 norefs) i32)))]
                             -> []
              local.get move 7 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
              local.get move 4 ;; [] ->
                                  [(ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
              load (path) move ;; [(ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep (sum (prod) ptr)) anyrefs)
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                                  ->
                                  [(ref (val ptr anyrefs) (base mm)
                                     (span (mem (rep (sum (prod) ptr)) norefs) (rep (sum (prod) ptr))))
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              local.set 8 ;; [(rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                             -> []
              drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep (sum (prod) ptr)) norefs) (rep (sum (prod) ptr))))]
                      -> []
              local.get move 8 ;; [] ->
                                  [(rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
              group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       ->
                       [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
              local.get copy 6 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum (val (sum (prod) ptr) anyrefs)
                                            (prod (val (prod) norefs))
                                            (ref (val ptr anyrefs) (base mm)
                                              (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                     -> (num (val i32 norefs) i32)))]
              call_indirect ;; [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                               (coderef (val i32 norefs)
                                 ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (rec (val (sum (prod) ptr) anyrefs)
                                      (sum (val (sum (prod) ptr) anyrefs)
                                        (prod (val (prod) norefs))
                                        (ref (val ptr anyrefs) (base mm)
                                          (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                 -> (num (val i32 norefs) i32)))]
                               -> [(num (val i32 norefs) i32)]
              local.get move 6 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum (val (sum (prod) ptr) anyrefs)
                                            (prod (val (prod) norefs))
                                            (ref (val ptr anyrefs) (base mm)
                                              (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                     -> (num (val i32 norefs) i32)))]
              drop ;; [(coderef (val i32 norefs)
                         ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                         -> (num (val i32 norefs) i32)))]
                      -> []
              local.get move 7 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
              drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
              local.get move 5 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
              drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                      (prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
                   -> [(num (val i32 norefs) i32)]
            i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
            local.get move 4 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
            drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> [])
        end ;; [(sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                  (ref (val ptr anyrefs) (base mm)
                    (ser (mem (rep (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> [])
      (func (-> (num (val i32 norefs) i32)) (local (prod i32 ptr) i32 ptr
          (sum (prod) ptr) (prod i32 ptr) i32 ptr (sum (prod) ptr) (prod i32 ptr) i32 ptr
          (sum (prod) ptr) (prod i32 ptr) i32 ptr)
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    ->
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       ->
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))]
                 [11 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [12 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [13 => (plug (val (prod i32) norefs) (prod i32))] [14 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 0 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              ->
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   ->
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 2 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 1 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                         -> []
          local.get move 2 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 6 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             ->
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           ->
                           [(rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          local.get move 1 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                  -> []
          local.get move 2 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               ->
               [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.set 3 ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       -> []
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    ->
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       ->
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 =>
                 (rec (val (sum (prod) ptr) anyrefs)
                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))]
                 [11 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [12 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [13 => (plug (val (prod i32) norefs) (prod i32))] [14 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 4 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              ->
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 4 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   ->
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 6 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                         -> []
          local.get move 6 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          num_const 7 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             ->
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           ->
                           [(rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                  -> []
          local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 4 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               ->
               [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.set 7 ;; [(rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                       -> []
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    ->
                    (rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                       ->
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))]
                 [11 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [12 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [13 => (plug (val (prod i32) norefs) (prod i32))] [14 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 8 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                              ->
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 8 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum (val (sum (prod) ptr) anyrefs)
                                            (prod (val (prod) norefs))
                                            (ref (val ptr anyrefs) (base mm)
                                              (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum (val (sum (prod) ptr) anyrefs)
                                            (prod (val (prod) norefs))
                                            (ref (val ptr anyrefs) (base mm)
                                              (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                   ->
                                   (rec (val (sum (prod) ptr) anyrefs)
                                     (sum (val (sum (prod) ptr) anyrefs)
                                       (prod (val (prod) norefs))
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                          ->
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                        ->
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 10 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 9 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                            ->
                            (rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                         -> []
          local.get move 10 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get move 3 ;; [] ->
                              [(rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          local.get move 7 ;; [] ->
                              [(rec (val (sum (prod) ptr) anyrefs)
                                 (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          group ;; [(rec (val (sum (prod) ptr) anyrefs)
                      (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                   (rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                   ->
                   [(prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
                   ->
                   [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          local.get copy 9 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          call_indirect ;; [(prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                             ->
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                           ->
                           [(rec (val (sum (prod) ptr) anyrefs)
                              (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          local.get move 9 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                                      (rec (val (sum (prod) ptr) anyrefs)
                                        (sum (val (sum (prod) ptr) anyrefs)
                                          (prod (val (prod) norefs))
                                          (ref (val ptr anyrefs) (base mm)
                                            (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                                 ->
                                 (rec (val (sum (prod) ptr) anyrefs)
                                   (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                     ->
                     (rec (val (sum (prod) ptr) anyrefs)
                       (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))]
                  -> []
          local.get move 10 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 8 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (prod (sum (prod) ptr) (sum (prod) ptr))) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (prod (val (prod (sum (prod) ptr) (sum (prod) ptr)) anyrefs)
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                      ->
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               ->
               [(rec (val (sum (prod) ptr) anyrefs)
                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
        local.set 11 ;; [(rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                        -> []
        coderef 2 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (rec (val (sum (prod) ptr) anyrefs)
                         (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (rec (val (sum (prod) ptr) anyrefs)
                            (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [4 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))]
                 [11 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [12 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [13 => (plug (val (prod i32) norefs) (prod i32))] [14 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 12 ;; [(prod (val (prod i32 ptr) anyrefs)
                             (coderef (val i32 norefs)
                               ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                  (rec (val (sum (prod) ptr) anyrefs)
                                    (sum (val (sum (prod) ptr) anyrefs)
                                      (prod (val (prod) norefs))
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                               -> (num (val i32 norefs) i32)))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                          -> []
          local.get move 12 ;; [] ->
                               [(prod (val (prod i32 ptr) anyrefs)
                                  (coderef (val i32 norefs)
                                    ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                       (rec (val (sum (prod) ptr) anyrefs)
                                         (sum (val (sum (prod) ptr) anyrefs)
                                           (prod (val (prod) norefs))
                                           (ref (val ptr anyrefs) (base mm)
                                             (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                    -> (num (val i32 norefs) i32)))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (rec (val (sum (prod) ptr) anyrefs)
                               (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (rec (val (sum (prod) ptr) anyrefs)
                             (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 14 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 13 ;; [(coderef (val i32 norefs)
                             ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                             -> (num (val i32 norefs) i32)))]
                          -> []
          local.get move 14 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get move 11 ;; [] ->
                               [(rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (rec (val (sum (prod) ptr) anyrefs)
                     (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0)))))]
                   ->
                   [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (rec (val (sum (prod) ptr) anyrefs)
                        (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))]
          local.get copy 13 ;; [] ->
                               [(coderef (val i32 norefs)
                                  ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                  -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (rec (val (sum (prod) ptr) anyrefs)
                                (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (rec (val (sum (prod) ptr) anyrefs)
                                  (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 13 ;; [] ->
                               [(coderef (val i32 norefs)
                                  ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                     (rec (val (sum (prod) ptr) anyrefs)
                                       (sum (val (sum (prod) ptr) anyrefs)
                                         (prod (val (prod) norefs))
                                         (ref (val ptr anyrefs) (base mm)
                                           (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                                  -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (rec (val (sum (prod) ptr) anyrefs)
                          (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 14 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 12 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr (sum (prod) ptr)) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (rec (val (sum (prod) ptr) anyrefs)
                           (sum (val (sum (prod) ptr) anyrefs)  (prod (val (prod) norefs))
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (sum (prod) ptr)) anyrefs) (var 0))))))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        local.get move 11 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        local.get move 7 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        local.get move 3 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> [])
      (table 0 1 2)
      (export "_start" (func 3)))
    -----------mini_zip-----------
    (module
      (func
          ((prod (val (prod ptr i32) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (num (val i32 norefs) i32))
          -> (num (val i32 norefs) i32)) (local ptr i32)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (num (val i32 norefs) i32))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (num (val i32 norefs) i32)]
        local.set 2 ;; [(num (val i32 norefs) i32)] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] -> [(num (val i32 norefs) i32)]
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> [])
      (func
          ((prod (val (prod ptr (prod i32 i32)) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))
          -> (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))) (local ptr
          (prod i32 i32) i32 i32 (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))]
        ungroup ;; [(prod (val (prod ptr (prod i32 i32)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32)))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        local.set 2 ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get copy 2 ;; [] ->
                            [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        ungroup ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] ->
                   [(num (val i32 norefs) i32) (num (val i32 norefs) i32)]
        local.set 4 ;; [(num (val i32 norefs) i32)] -> []
        local.set 3 ;; [(num (val i32 norefs) i32)] -> []
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
                 [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                 [2 => (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
                 [3 => (num (val i32 norefs) i32)] [4 => (num (val i32 norefs) i32)]
                 [5 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 5 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 5 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 7 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 6 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 7 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get copy 3 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 6 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 6 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 7 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 5 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))]
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        group ;; [(coderef (val i32 norefs)
                    ((prod (val (prod ptr i32) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                       (num (val i32 norefs) i32))
                    -> (num (val i32 norefs) i32)))
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                 [(prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
        pack ;; [(prod (val (prod i32 ptr) anyrefs)
                   (coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                   (prod (val (prod i32 ptr) anyrefs)
                     (coderef (val i32 norefs)
                       ((prod (val (prod ptr i32) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                          (num (val i32 norefs) i32))
                       -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
        unpack (localfx [0 => (plug (val (prod i32 i32 i32) norefs) (prod i32 i32 i32))]
                 [1 => (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
                 [2 => (prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
                 [3 => (num (val i32 norefs) i32)] [4 => (num (val i32 norefs) i32)]
                 [5 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                 [8 => (plug (val (prod i32 i32) norefs) (prod i32 i32))]
                 [9 => (plug (val (prod i32) norefs) (prod i32))] [10 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 8 ;; [(prod (val (prod i32 ptr) anyrefs)
                            (coderef (val i32 norefs)
                              ((prod (val (prod ptr i32) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                 (num (val i32 norefs) i32))
                              -> (num (val i32 norefs) i32)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                         -> []
          local.get move 8 ;; [] ->
                              [(prod (val (prod i32 ptr) anyrefs)
                                 (coderef (val i32 norefs)
                                   ((prod (val (prod ptr i32) anyrefs)
                                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                      (num (val i32 norefs) i32))
                                   -> (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
          ungroup ;; [(prod (val (prod i32 ptr) anyrefs)
                        (coderef (val i32 norefs)
                          ((prod (val (prod ptr i32) anyrefs)
                             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                             (num (val i32 norefs) i32))
                          -> (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0))))]
                     ->
                     [(coderef (val i32 norefs)
                        ((prod (val (prod ptr i32) anyrefs)
                           (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                           (num (val i32 norefs) i32))
                        -> (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.set 10 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))] -> []
          local.set 9 ;; [(coderef (val i32 norefs)
                            ((prod (val (prod ptr i32) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                               (num (val i32 norefs) i32))
                            -> (num (val i32 norefs) i32)))]
                         -> []
          local.get move 10 ;; [] -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))]
          local.get copy 4 ;; [] -> [(num (val i32 norefs) i32)]
          group ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                   (num (val i32 norefs) i32)] ->
                   [(prod (val (prod ptr i32) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                      (num (val i32 norefs) i32))]
          local.get copy 9 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          call_indirect ;; [(prod (val (prod ptr i32) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                              (num (val i32 norefs) i32))
                           (coderef (val i32 norefs)
                             ((prod (val (prod ptr i32) anyrefs)
                                (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                (num (val i32 norefs) i32))
                             -> (num (val i32 norefs) i32)))]
                           -> [(num (val i32 norefs) i32)]
          local.get move 9 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((prod (val (prod ptr i32) anyrefs)
                                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                                    (num (val i32 norefs) i32))
                                 -> (num (val i32 norefs) i32)))]
          drop ;; [(coderef (val i32 norefs)
                     ((prod (val (prod ptr i32) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                        (num (val i32 norefs) i32))
                     -> (num (val i32 norefs) i32)))]
                  -> []
          local.get move 10 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
          drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
          local.get move 8 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
          drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val (prod) norefs)
                  (prod (val (prod i32 ptr) anyrefs)
                    (coderef (val i32 norefs)
                      ((prod (val (prod ptr i32) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))
                         (num (val i32 norefs) i32))
                      -> (num (val i32 norefs) i32)))
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (var 0)))))]
               -> [(num (val i32 norefs) i32)]
        group ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] ->
                 [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        local.get move 3 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 4 ;; [] -> [(num (val i32 norefs) i32)]
        drop ;; [(num (val i32 norefs) i32)] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))]
        drop ;; [(prod (val (prod i32 i32) norefs) (num (val i32 norefs) i32) (num (val i32 norefs) i32))] -> [])
      (func
          ((prod (val (prod ptr (prod ptr ptr)) anyrefs)
             (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
             (prod (val (prod ptr ptr) anyrefs)
               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
               (ref (val ptr anyrefs) (base mm)
                 (ser (mem (rep ptr) anyrefs)
                   (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))))
          ->
          (ref (val ptr anyrefs) (base mm)
            (ser (mem (rep (prod i32 ptr)) anyrefs)
              (prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))))
          (local ptr (prod ptr ptr) ptr ptr i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (val (prod ptr (prod ptr ptr)) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                               (prod (val (prod ptr ptr) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                                 (ref (val ptr anyrefs) (base mm)
                                   (ser (mem (rep ptr) anyrefs)
                                     (ref (val ptr anyrefs) (base mm)
                                       (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))))]
        ungroup ;; [(prod (val (prod ptr (prod ptr ptr)) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                      (prod (val (prod ptr ptr) anyrefs)
                        (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                        (ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep ptr) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))
                   (prod (val (prod ptr ptr) anyrefs)
                     (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                     (ref (val ptr anyrefs) (base mm)
                       (ser (mem (rep ptr) anyrefs)
                         (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))))]
        local.set 2 ;; [(prod (val (prod ptr ptr) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                          (ref (val ptr anyrefs) (base mm)
                            (ser (mem (rep ptr) anyrefs)
                              (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))))]
                       -> []
        local.set 1 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] ->
                            [(prod (val (prod ptr ptr) anyrefs)
                               (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                               (ref (val ptr anyrefs) (base mm)
                                 (ser (mem (rep ptr) anyrefs)
                                   (ref (val ptr anyrefs) (base mm)
                                     (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))))]
        ungroup ;; [(prod (val (prod ptr ptr) anyrefs)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                      (ref (val ptr anyrefs) (base mm)
                        (ser (mem (rep ptr) anyrefs)
                          (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))))]
                   -> [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))
                   (ref (val ptr anyrefs) (base mm)
                     (ser (mem (rep ptr) anyrefs)
                       (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
        local.set 4 ;; [(ref (val ptr anyrefs) (base mm)
                          (ser (mem (rep ptr) anyrefs)
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
                       -> []
        local.set 3 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        local.get move 3 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] ->
                            [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))
                            (num (val i32 norefs) i32)]
        local.set 5 ;; [(num (val i32 norefs) i32)] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep i32) norefs) (rep i32)))] -> []
        local.get move 5 ;; [] -> [(num (val i32 norefs) i32)]
        local.get move 4 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep ptr) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
        load (path) move ;; [(ref (val ptr anyrefs) (base mm)
                               (ser (mem (rep ptr) anyrefs)
                                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))))]
                            -> [(ref (val ptr anyrefs) (base mm) (span (mem (rep ptr) norefs) (rep ptr)))
                            (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        local.set 6 ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] -> []
        drop ;; [(ref (val ptr anyrefs) (base mm) (span (mem (rep ptr) norefs) (rep ptr)))] -> []
        local.get move 6 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))]
        group ;; [(num (val i32 norefs) i32)
                 (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32)))] ->
                 [(prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                    (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
        new ;; [(prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                  (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))]
               ->
               [(ref (val ptr anyrefs) (base mm)
                  (ser (mem (rep (prod i32 ptr)) anyrefs)
                    (prod (val (prod i32 ptr) anyrefs) (num (val i32 norefs) i32)
                      (ref (val ptr anyrefs) (base mm) (ser (mem (rep i32) norefs) (num (val i32 norefs) i32))))))]
        local.get move 3 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 4 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        drop ;; [(ref (val ptr anyrefs) (base mm) (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] -> []
        local.get move 2 ;; [] -> [(plug (val (prod i32 i32) norefs) (prod i32 i32))]
        drop ;; [(plug (val (prod i32 i32) norefs) (prod i32 i32))] -> [])
      (table 0 1 2)
      (export "typle_add1" (func 1))) |xxx}]
