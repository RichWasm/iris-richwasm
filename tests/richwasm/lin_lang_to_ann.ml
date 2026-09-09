open! Core
open! Stdlib.Format
open! Test_support
open Richwasm_support.Pipeline
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Richwasm_lin_lang

  type syntax = Syntax.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let syntax_pipeline x = ll_pipeline x |> elab_pipeline
  let string_pipeline s = ll_str_pipeline s |> elab_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = AnnRichWasm.Module.pp
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {xxx|
    (module
      (func (-> (num i32))
        num_const 1 ;; [] -> [(num i32)])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (InnerFunT (MonoFunT () ((NumT (IntT I32T)))))) (mf_locals ())
        (mf_body ((INumConst (InstrT () ((NumT (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {xxx|
    (module
      (func (-> (prod (num i32) (num i32) (num i32) (num i32)))
        num_const 1 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        num_const 3 ;; [] -> [(num i32)]
        num_const 4 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32) (num i32) (num i32)] -> [(prod (num i32) (num i32) (num i32) (num i32))])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type
         (InnerFunT (MonoFunT () ((ProdT ((NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T))))))))
        (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (IntT I32T)))) 1) (INumConst (InstrT () ((NumT (IntT I32T)))) 2)
          (INumConst (InstrT () ((NumT (IntT I32T)))) 3) (INumConst (InstrT () ((NumT (IntT I32T)))) 4)
          (IGroup
           (InstrT ((NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T)))
            ((ProdT ((NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T)) (NumT (IntT I32T))))))))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  run {| (tup (tup 1 (tup 2 3) 4 5) (tup 6 7)) |};
  [%expect
    {xxx|
    (module
      (func (-> (prod (prod (num i32) (prod (num i32) (num i32)) (num i32) (num i32)) (prod (num i32) (num i32))))
        num_const 1 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        num_const 3 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
        num_const 4 ;; [] -> [(num i32)]
        num_const 5 ;; [] -> [(num i32)]
        group ;; [(num i32) (prod (num i32) (num i32)) (num i32) (num i32)] ->
                 [(prod (num i32) (prod (num i32) (num i32)) (num i32) (num i32))]
        num_const 6 ;; [] -> [(num i32)]
        num_const 7 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
        group ;; [(prod (num i32) (prod (num i32) (num i32)) (num i32) (num i32)) (prod (num i32) (num i32))] ->
                 [(prod (prod (num i32) (prod (num i32) (num i32)) (num i32) (num i32)) (prod (num i32) (num i32)))])
      (table)
      (export "_start" (func 0))) |xxx}];

  run {| (new 10) |};
  [%expect
    {xxx|
    (module
      (func (-> (ref (base mm) mut (ser (num i32))))
        num_const 10 ;; [] -> [(num i32)]
        new ;; [(num i32)] -> [(ref (base mm) mut (ser (num i32)))])
      (table)
      (export "_start" (func 0))) |xxx}];

  run {| (1 + 2) |};
  [%expect
    {xxx|
    (module
      (func (-> (num i32))
        num_const 1 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0))) |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (InnerFunT (MonoFunT () ((NumT (IntT I32T)))))) (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (IntT I32T)))) 1) (INumConst (InstrT () ((NumT (IntT I32T)))) 2)
          (INum (InstrT ((NumT (IntT I32T)) (NumT (IntT I32T))) ((NumT (IntT I32T)))) (IInt2 I32T AddI)))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

  (* [%expect {| |}]; *)
  ()

let%expect_test "examples" =
  output_examples ();
  [%expect
    {xxx|
    -----------one-----------
    (module
      (func (-> (num i32))
        num_const 1 ;; [] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------flat_tuple-----------
    (module
      (func (-> (prod (num i32) (num i32) (num i32) (num i32)))
        num_const 1 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        num_const 3 ;; [] -> [(num i32)]
        num_const 4 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32) (num i32) (num i32)] -> [(prod (num i32) (num i32) (num i32) (num i32))])
      (table)
      (export "_start" (func 0)))
    -----------nested_tuple-----------
    (module
      (func (-> (prod (prod (num i32) (num i32)) (prod (num i32) (num i32))))
        num_const 1 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
        num_const 3 ;; [] -> [(num i32)]
        num_const 4 ;; [] -> [(num i32)]
        group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
        group ;; [(prod (num i32) (num i32)) (prod (num i32) (num i32))] ->
                 [(prod (prod (num i32) (num i32)) (prod (num i32) (num i32)))])
      (table)
      (export "_start" (func 0)))
    -----------single_sum-----------
    (module
      (func (-> (sum  (prod)))
        group ;; [] -> [(prod)]
        inject 0 ;; [(prod)] -> [(sum  (prod))])
      (table)
      (export "_start" (func 0)))
    -----------double_sum-----------
    (module
      (func (-> (sum  (prod) (num i32)))
        num_const 15 ;; [] -> [(num i32)]
        inject 1 ;; [(num i32)] -> [(sum  (prod) (num i32))])
      (table)
      (export "_start" (func 0)))
    -----------arith_add-----------
    (module
      (func (-> (num i32))
        num_const 9 ;; [] -> [(num i32)]
        num_const 10 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_sub-----------
    (module
      (func (-> (num i32))
        num_const 67 ;; [] -> [(num i32)]
        num_const 41 ;; [] -> [(num i32)]
        i32.sub ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_mul-----------
    (module
      (func (-> (num i32))
        num_const 42 ;; [] -> [(num i32)]
        num_const 10 ;; [] -> [(num i32)]
        i32.mul ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------arith_div-----------
    (module
      (func (-> (num i32))
        num_const -30 ;; [] -> [(num i32)]
        num_const 10 ;; [] -> [(num i32)]
        i32.div_s ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------app_ident-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod) i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        load (path) move ;; [(ref (base mm) mut (ser (prod)))] -> [(ref (base mm) mut (span (rep (prod)))) (prod)]
        local.set 3 ;; [(prod)] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod))))] -> []
        local.get move 3 ;; [] -> [(prod)]
        ungroup ;; [(prod)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 0 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 10 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)])
      (table 0)
      (export "_start" (func 1)))
    -----------nested_arith-----------
    (module
      (func (-> (num i32))
        num_const 9 ;; [] -> [(num i32)]
        num_const 10 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        num_const 5 ;; [] -> [(num i32)]
        i32.mul ;; [(num i32) (num i32)] -> [(num i32)])
      (table)
      (export "_start" (func 0)))
    -----------let_bind-----------
    (module
      (func (-> (num i32)) (local i32)
        num_const 10 ;; [] -> [(num i32)]
        local.set 0 ;; [(num i32)] -> []
        local.get copy 0 ;; [] -> [(num i32)]
        local.get move 0 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (table)
      (export "_start" (func 0)))
    -----------add_one_program-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 0 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 42 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)])
      (table 0)
      (export "add-one" (func 0))
      (export "_start" (func 1)))
    -----------add_tup_ref-----------
    (module
      (func (-> (num i32)) (local ptr i32 ptr i32 i32)
        num_const 2 ;; [] -> [(num i32)]
        new ;; [(num i32)] -> [(ref (base mm) mut (ser (num i32)))]
        local.set 0 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        num_const 1 ;; [] -> [(num i32)]
        local.get move 0 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        group ;; [(num i32) (ref (base mm) mut (ser (num i32)))] -> [(prod (num i32) (ref (base mm) mut (ser (num i32))))]
        ungroup ;; [(prod (num i32) (ref (base mm) mut (ser (num i32))))] ->
                   [(num i32) (ref (base mm) mut (ser (num i32)))]
        local.set 2 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.set 1 ;; [(num i32)] -> []
        local.get move 2 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        load (path) move ;; [(ref (base mm) mut (ser (num i32)))] -> [(ref (base mm) mut (span (rep i32))) (num i32)]
        local.set 3 ;; [(num i32)] -> []
        drop ;; [(ref (base mm) mut (span (rep i32)))] -> []
        local.get move 3 ;; [] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 1 ;; [] -> [(num i32)]
        local.get copy 4 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 2 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 0 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> [])
      (table)
      (export "_start" (func 0)))
    -----------print_10-----------
    (module
      (import ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod)))
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod))
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        call 0 (inst) ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(prod)])
      (func (-> (prod)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod))) (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (prod)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (prod))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (prod))) (var 0))] -> []
          local.get move 0 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (prod))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (prod))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (prod))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (num i32)) -> (prod)))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 10 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (prod)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (prod)))] -> [(prod)]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (prod)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (prod)))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (prod))) (var 0)))]
               -> [(prod)])
      (table 0)
      (export "_start" (func 2)))
    -----------closure-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod (num i32)))) (prod)) -> (num i32)) (local ptr
          (prod) (prod i32) i32 (prod))
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod (num i32)))) (prod))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod (num i32)))) (prod))] ->
                   [(ref (base mm) mut (ser (prod (num i32)))) (prod)]
        local.set 2 ;; [(prod)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod (num i32))))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod (num i32))))]
        load (path) move ;; [(ref (base mm) mut (ser (prod (num i32))))] ->
                            [(ref (base mm) mut (span (rep (prod i32)))) (prod (num i32))]
        local.set 3 ;; [(prod (num i32))] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod i32))))] -> []
        local.get move 3 ;; [] -> [(prod (num i32))]
        ungroup ;; [(prod (num i32))] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 2 ;; [] -> [(prod)]
        local.set 5 ;; [(prod)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        local.get move 5 ;; [] -> [(prod)]
        drop ;; [(prod)] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(prod)]
        drop ;; [(prod)] -> [])
      (func (-> (num i32)) (local i32 (prod i32 ptr) i32 ptr)
        num_const 10 ;; [] -> [(num i32)]
        local.set 0 ;; [(num i32)] -> []
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (prod)) -> (num i32)))]
        local.get copy 0 ;; [] -> [(num i32)]
        group ;; [(num i32)] -> [(prod (num i32))]
        new ;; [(prod (num i32))] -> [(ref (base mm) mut (ser (prod (num i32))))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (prod)) -> (num i32)))
                  (ref (base mm) mut (ser (prod (num i32))))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (prod)) -> (num i32)))
                    (ref (base mm) mut (ser (prod (num i32)))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (prod)) -> (num i32)))
                   (ref (base mm) mut (ser (prod (num i32)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (num i32)] [1 => (plug (prod i32 i32))] [2 => (plug (prod i32))] [3 => (plug (prod i32))])
          local.set 1 ;; [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))] -> []
          local.get move 1 ;; [] -> [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.set 2 ;; [(coderef ((prod (var 0) (prod)) -> (num i32)))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          group ;; [] -> [(prod)]
          group ;; [(var 0) (prod)] -> [(prod (var 0) (prod))]
          local.get copy 2 ;; [] -> [(coderef ((prod (var 0) (prod)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (prod)) (coderef ((prod (var 0) (prod)) -> (num i32)))] -> [(num i32)]
          local.get move 2 ;; [] -> [(coderef ((prod (var 0) (prod)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (prod)) -> (num i32)))] -> []
          local.get move 3 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 1 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 0 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (table 0)
      (export "_start" (func 1)))
    -----------closure_call_var-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)) (local ptr i32 (prod i32) i32 i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod (num i32)))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod (num i32)))) (num i32))] ->
                   [(ref (base mm) mut (ser (prod (num i32)))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod (num i32))))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod (num i32))))]
        load (path) move ;; [(ref (base mm) mut (ser (prod (num i32))))] ->
                            [(ref (base mm) mut (span (rep (prod i32)))) (prod (num i32))]
        local.set 3 ;; [(prod (num i32))] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod i32))))] -> []
        local.get move 3 ;; [] -> [(prod (num i32))]
        ungroup ;; [(prod (num i32))] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 5 ;; [(num i32)] -> []
        local.get copy 5 ;; [] -> [(num i32)]
        local.get copy 4 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 5 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local i32 i32 (prod i32 ptr) i32 ptr)
        num_const 21 ;; [] -> [(num i32)]
        local.set 0 ;; [(num i32)] -> []
        num_const 1 ;; [] -> [(num i32)]
        local.set 1 ;; [(num i32)] -> []
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))]
        local.get copy 1 ;; [] -> [(num i32)]
        group ;; [(num i32)] -> [(prod (num i32))]
        new ;; [(prod (num i32))] -> [(ref (base mm) mut (ser (prod (num i32))))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod (num i32))))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod (num i32)))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod (num i32)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (num i32)] [1 => (num i32)] [2 => (plug (prod i32 i32))]
                 [3 => (plug (prod i32))] [4 => (plug (prod i32))])
          local.set 2 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 2 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.set 3 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 4 ;; [] -> [(var 0)]
          local.get copy 0 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 3 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 3 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 4 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 1 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 0 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (table 0)
      (export "_start" (func 1)))
    -----------mk_id_tl_anf-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
          (local ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr (prod i32 ptr) (prod i32 ptr) i32 ptr)
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                     (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                       (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0) (num i32)) ->
                       (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                         (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0) (num i32)) ->
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0) (num i32)) ->
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0) (num i32)) ->
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0) (num i32)) ->
                            (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 0 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
          call_indirect ;; [(prod (var 0) (num i32))
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                           ->
                           [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
          drop ;; [(coderef
                     ((prod (var 0) (num i32)) ->
                     (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                       (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0) (num i32)) ->
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                    (var 0)))]
               ->
               [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        local.set 3 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 4 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 4 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.set 5 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          num_const 10 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 5 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 5 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 6 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 4 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 3 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (table 0 1)
      (export "_start" (func 2)))
    -----------triangle_tl-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
            [5 => (plug (prod i32))])
          num_const 0 ;; [] -> [(num i32)]
        else
          local.get copy 2 ;; [] -> [(num i32)]
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
                   [5 => (plug (prod i32))])
            local.set 3 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
            local.get move 3 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
            ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                       [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
            local.set 5 ;; [(var 0)] -> []
            local.set 4 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 5 ;; [] -> [(var 0)]
            local.get copy 2 ;; [] -> [(num i32)]
            num_const 1 ;; [] -> [(num i32)]
            i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
            local.get move 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 5 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                 -> [(num i32)]
          i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        end ;; [(num i32)] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 0 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 10 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)])
      (table 0)
      (export "_start" (func 1)))
    -----------factorial_tl-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 i32 (prod i32 ptr) i32 ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (num i32)] [3 => (plug (prod i32))] [4 => (plug (prod i32 i32))]
            [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))])
          num_const 1 ;; [] -> [(num i32)]
        else
          local.get copy 2 ;; [] -> [(num i32)]
          num_const 1 ;; [] -> [(num i32)]
          i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
          local.set 3 ;; [(num i32)] -> []
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (num i32)] [3 => (num i32)] [4 => (plug (prod i32 i32))]
                   [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))])
            local.set 4 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
            local.get move 4 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
            ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                       [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
            local.set 6 ;; [(var 0)] -> []
            local.set 5 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 6 ;; [] -> [(var 0)]
            local.get copy 3 ;; [] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 5 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
            local.get move 5 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 6 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 4 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                 -> [(num i32)]
          local.set 7 ;; [(num i32)] -> []
          local.get copy 2 ;; [] -> [(num i32)]
          local.get copy 7 ;; [] -> [(num i32)]
          i32.mul ;; [(num i32) (num i32)] -> [(num i32)]
          local.get move 7 ;; [] -> [(num i32)]
          drop ;; [(num i32)] -> []
          local.get move 3 ;; [] -> [(num i32)]
          drop ;; [(num i32)] -> []
        end ;; [(num i32)] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 0 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 5 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)])
      (table 0)
      (export "factorial" (func 0))
      (export "_start" (func 1)))
    -----------safe_div-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))) (local ptr
          (prod i32 i32) i32 i32 i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32)))] ->
                   [(ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))]
        local.set 2 ;; [(prod (num i32) (num i32))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(prod (num i32) (num i32))]
        ungroup ;; [(prod (num i32) (num i32))] -> [(num i32) (num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.set 3 ;; [(num i32)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (prod (num i32) (num i32))] [3 => (num i32)] [4 => (num i32)]
            [5 => (plug (prod i32))])
          group ;; [] -> [(prod)]
          inject 1 ;; [(prod)] -> [(sum  (num i32) (prod))]
        else
          local.get copy 3 ;; [] -> [(num i32)]
          local.get copy 4 ;; [] -> [(num i32)]
          i32.div_s ;; [(num i32) (num i32)] -> [(num i32)]
          local.set 5 ;; [(num i32)] -> []
          local.get copy 5 ;; [] -> [(num i32)]
          inject 0 ;; [(num i32)] -> [(sum  (num i32) (prod))]
          local.get move 5 ;; [] -> [(num i32)]
          drop ;; [(num i32)] -> []
        end ;; [(num i32)] -> [(sum  (num i32) (prod))]
        local.get move 3 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(prod (num i32) (num i32))]
        drop ;; [(prod (num i32) (num i32))] -> [])
      (func ((prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))) -> (num i32)) (local ptr
          (sum i32 (prod)) i32 (prod))
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod)))] ->
                   [(ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))]
        local.set 2 ;; [(sum  (num i32) (prod))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(sum  (num i32) (prod))]
        case
          (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (sum  (num i32) (prod))] [3 => (plug (prod i32))] [4 => (plug (prod))])
          (0
            local.set 3 ;; [(num i32)] -> []
            local.get copy 3 ;; [] -> [(num i32)]
            local.get move 3 ;; [] -> [(num i32)]
            drop ;; [(num i32)] -> [])
          (1
            local.set 4 ;; [(prod)] -> []
            num_const 0 ;; [] -> [(num i32)]
            local.get move 4 ;; [] -> [(prod)]
            drop ;; [(prod)] -> [])
        end ;; [(sum  (num i32) (prod))] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(sum  (num i32) (prod))]
        drop ;; [(sum  (num i32) (prod))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr (sum i32 (prod)) (prod i32 ptr) i32 ptr)
        coderef 0 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod)))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 0 ;; [(prod (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod)))) (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))
                                 (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod)))) (var 0))] ->
                     [(coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod)))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 10 ;; [] -> [(num i32)]
          num_const 0 ;; [] -> [(num i32)]
          group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
          group ;; [(var 0) (prod (num i32) (num i32))] -> [(prod (var 0) (prod (num i32) (num i32)))]
          local.get copy 1 ;; [] -> [(coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))]
          call_indirect ;; [(prod (var 0) (prod (num i32) (num i32)))
                            (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))]
                           -> [(sum  (num i32) (prod))]
          local.get move 1 ;; [] -> [(coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))]
          drop ;; [(coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod))))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (prod (num i32) (num i32))) -> (sum  (num i32) (prod)))) (var 0)))]
               -> [(sum  (num i32) (prod))]
        local.set 3 ;; [(sum  (num i32) (prod))] -> []
        coderef 1 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (sum  (num i32) (prod))) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (sum  (num i32) (prod))]
                 [4 => (plug (prod i32 i32))] [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 4 ;; [(prod (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0))] -> []
          local.get move 4 ;; [] -> [(prod (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.set 5 ;; [(coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32)))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          local.get copy 3 ;; [] -> [(sum  (num i32) (prod))]
          group ;; [(var 0) (sum  (num i32) (prod))] -> [(prod (var 0) (sum  (num i32) (prod)))]
          local.get copy 5 ;; [] -> [(coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (sum  (num i32) (prod)))
                            (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32)))]
                           -> [(num i32)]
          local.get move 5 ;; [] -> [(coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32)))] -> []
          local.get move 6 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 4 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (sum  (num i32) (prod))) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 3 ;; [] -> [(sum  (num i32) (prod))]
        drop ;; [(sum  (num i32) (prod))] -> [])
      (table 0 1)
      (export "_start" (func 2)))
    -----------incr_n-----------
    (module
      (func
          ((prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))) ->
          (ref (base mm) mut (ser (num i32)))) (local ptr ptr ptr i32 ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32))))] ->
                   [(ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))]
        local.set 2 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        num_const 0 ;; [] -> [(num i32)]
        swap (path) ;; [(ref (base mm) mut (ser (num i32))) (num i32)] -> [(ref (base mm) mut (ser (num i32))) (num i32)]
        group ;; [(ref (base mm) mut (ser (num i32))) (num i32)] -> [(prod (ref (base mm) mut (ser (num i32))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (num i32))) (num i32))] ->
                   [(ref (base mm) mut (ser (num i32))) (num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.set 3 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.get move 3 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        local.get copy 4 ;; [] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        swap (path) ;; [(ref (base mm) mut (ser (num i32))) (num i32)] -> [(ref (base mm) mut (ser (num i32))) (num i32)]
        group ;; [(ref (base mm) mut (ser (num i32))) (num i32)] -> [(prod (ref (base mm) mut (ser (num i32))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (num i32))) (num i32))] ->
                   [(ref (base mm) mut (ser (num i32))) (num i32)]
        local.set 6 ;; [(num i32)] -> []
        local.set 5 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.get move 5 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        local.get move 5 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 6 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 3 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> [])
      (func ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32))
          (local ptr (prod ptr i32) ptr i32 i32 (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32)))] ->
                   [(ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))]
        local.set 2 ;; [(prod (ref (base mm) mut (ser (num i32))) (num i32))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(prod (ref (base mm) mut (ser (num i32))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (num i32))) (num i32))] ->
                   [(ref (base mm) mut (ser (num i32))) (num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.set 3 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (plug (prod i32 i32))] [3 => (plug (prod i32))] [4 => (num i32)]
            [5 => (plug (prod i32))] [6 => (plug (prod i32 i32))] [7 => (plug (prod i32))]
            [8 => (plug (prod i32))] [9 => (plug (prod i32 i32))] [10 => (plug (prod i32))]
            [11 => (plug (prod i32))])
          local.get move 3 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
          load (path) move ;; [(ref (base mm) mut (ser (num i32)))] -> [(ref (base mm) mut (span (rep i32))) (num i32)]
          local.set 5 ;; [(num i32)] -> []
          drop ;; [(ref (base mm) mut (span (rep i32)))] -> []
          local.get move 5 ;; [] -> [(num i32)]
        else
          coderef 1 ;; [] ->
                       [(coderef
                          ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                          (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef
                      ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                      (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod
                      (coderef
                        ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                        (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod
                     (coderef
                       ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                       (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                       (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (plug (prod i32 i32))] [3 => (plug (prod i32))]
                   [4 => (num i32)] [5 => (plug (prod i32))] [6 => (plug (prod i32 i32))]
                   [7 => (plug (prod i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32 i32))]
                   [10 => (plug (prod i32))] [11 => (plug (prod i32))])
            local.set 6 ;; [(prod
                              (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                              (var 0))]
                           -> []
            local.get move 6 ;; [] ->
                                [(prod
                                   (coderef
                                     ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                                   (var 0))]
            ungroup ;; [(prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                          (var 0))]
                       ->
                       [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                        (var 0)]
            local.set 8 ;; [(var 0)] -> []
            local.set 7 ;; [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
                           -> []
            local.get move 8 ;; [] -> [(var 0)]
            coderef 0 ;; [] ->
                         [(coderef
                            ((prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))) ->
                            (ref (base mm) mut (ser (num i32)))))]
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
            group ;; [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))) ->
                        (ref (base mm) mut (ser (num i32)))))
                      (ref (base mm) mut (ser (prod)))]
                     ->
                     [(prod
                        (coderef
                          ((prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))) ->
                          (ref (base mm) mut (ser (num i32)))))
                        (ref (base mm) mut (ser (prod))))]
            pack ;; [(prod
                       (coderef
                         ((prod (ref (base mm) mut (ser (prod))) (ref (base mm) mut (ser (num i32)))) ->
                         (ref (base mm) mut (ser (num i32)))))
                       (ref (base mm) mut (ser (prod))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                       (prod
                         (coderef
                           ((prod (var 0) (ref (base mm) mut (ser (num i32)))) -> (ref (base mm) mut (ser (num i32)))))
                         (var 0)))]
            unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                     [2 => (plug (prod i32 i32))] [3 => (plug (prod i32))]
                     [4 => (num i32)] [5 => (plug (prod i32))] [6 => (plug (prod i32 i32))]
                     [7 => (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
                     [8 => (plug (prod i32))] [9 => (plug (prod i32 i32))]
                     [10 => (plug (prod i32))] [11 => (plug (prod i32))])
              local.set 9 ;; [(prod
                                (coderef
                                  ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                  (ref (base mm) mut (ser (num i32)))))
                                (var 0))]
                             -> []
              local.get move 9 ;; [] ->
                                  [(prod
                                     (coderef
                                       ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                       (ref (base mm) mut (ser (num i32)))))
                                     (var 0))]
              ungroup ;; [(prod
                            (coderef
                              ((prod (var 0) (ref (base mm) mut (ser (num i32)))) -> (ref (base mm) mut (ser (num i32)))))
                            (var 0))]
                         ->
                         [(coderef
                            ((prod (var 0) (ref (base mm) mut (ser (num i32)))) -> (ref (base mm) mut (ser (num i32)))))
                          (var 0)]
              local.set 11 ;; [(var 0)] -> []
              local.set 10 ;; [(coderef
                                 ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                 (ref (base mm) mut (ser (num i32)))))]
                              -> []
              local.get move 11 ;; [] -> [(var 0)]
              local.get move 3 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
              group ;; [(var 0) (ref (base mm) mut (ser (num i32)))] ->
                       [(prod (var 0) (ref (base mm) mut (ser (num i32))))]
              local.get copy 10 ;; [] ->
                                   [(coderef
                                      ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                      (ref (base mm) mut (ser (num i32)))))]
              call_indirect ;; [(prod (var 0) (ref (base mm) mut (ser (num i32))))
                                (coderef
                                  ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                  (ref (base mm) mut (ser (num i32)))))]
                               -> [(ref (base mm) mut (ser (num i32)))]
              local.get move 10 ;; [] ->
                                   [(coderef
                                      ((prod (var 0) (ref (base mm) mut (ser (num i32)))) ->
                                      (ref (base mm) mut (ser (num i32)))))]
              drop ;; [(coderef
                         ((prod (var 0) (ref (base mm) mut (ser (num i32)))) -> (ref (base mm) mut (ser (num i32)))))]
                      -> []
              local.get move 11 ;; [] -> [(plug (prod i32))]
              drop ;; [(plug (prod i32))] -> []
              local.get move 9 ;; [] -> [(plug (prod i32 i32))]
              drop ;; [(plug (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod
                        (coderef
                          ((prod (var 0) (ref (base mm) mut (ser (num i32)))) -> (ref (base mm) mut (ser (num i32)))))
                        (var 0)))]
                   -> [(ref (base mm) mut (ser (num i32)))]
            local.get copy 4 ;; [] -> [(num i32)]
            num_const 1 ;; [] -> [(num i32)]
            i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
            group ;; [(ref (base mm) mut (ser (num i32))) (num i32)] ->
                     [(prod (ref (base mm) mut (ser (num i32))) (num i32))]
            group ;; [(var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))] ->
                     [(prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32)))]
            local.get copy 7 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
            call_indirect ;; [(prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32)))
                              (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
                             -> [(num i32)]
            local.get move 7 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
            drop ;; [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))] -> []
            local.get move 8 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 6 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                      (var 0)))]
                 -> [(num i32)]
        end ;; [(num i32)] -> [(num i32)]
        local.get move 3 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (func (-> (num i32)) (local ptr (prod i32 ptr) i32 ptr)
        num_const 10 ;; [] -> [(num i32)]
        new ;; [(num i32)] -> [(ref (base mm) mut (ser (num i32)))]
        local.set 0 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                        (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                    (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                      (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod))) (prod (ref (base mm) mut (ser (num i32))) (num i32))) ->
                     (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32))] [1 => (plug (prod i32 i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))])
          local.set 1 ;; [(prod
                            (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                            (var 0))]
                         -> []
          local.get move 1 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                                 (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32))) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.set 2 ;; [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))] ->
                         []
          local.get move 3 ;; [] -> [(var 0)]
          local.get move 0 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
          num_const 3 ;; [] -> [(num i32)]
          group ;; [(ref (base mm) mut (ser (num i32))) (num i32)] ->
                   [(prod (ref (base mm) mut (ser (num i32))) (num i32))]
          group ;; [(var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))] ->
                   [(prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32)))]
          local.get copy 2 ;; [] ->
                              [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32)))
                            (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
                           -> [(num i32)]
          local.get move 2 ;; [] ->
                              [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))] -> []
          local.get move 3 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 1 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (prod (ref (base mm) mut (ser (num i32))) (num i32))) -> (num i32)))
                    (var 0)))]
               -> [(num i32)]
        local.get move 0 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> [])
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
                 ((Var 0)
                  (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                   (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Var 1))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Var 0)))))))
                      (Var 0))))))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Var 0)))))))
             (Var 0))))
          (Plug (Prod ((Atom I32) (Atom I32)))))))
       (instr
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Var 0) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Var 0)))))))
             (Var 0)))))))
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) AnyRefs)))
         (labels
          (((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
             (Prod
              ((CodeRef
                (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                 ((Num (Int I32)))))
               (Var 0)))))))
         (return
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Var 0)
                           (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod ((Var 0) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Var 0)))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Var 0)))))))
                      (Var 0))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType () ((Prod ((Var 0) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                       (Prod
                        ((CodeRef
                          (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Var 0)))))))
                   (Var 0))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Var 0)
                       (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Var 0)))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Var 0)))))))
                  (Var 0)))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Var 0))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Var 0)))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Var 0)
                           (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod ((Var 0) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Var 0)))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Var 0)))))))
                      (Var 0))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType () ((Prod ((Var 0) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                       (Prod
                        ((CodeRef
                          (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Var 0)))))))
                   (Var 0))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Var 0)
                       (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Var 0)))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Var 0)))))))
                  (Var 0)))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Var 0))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) Mut (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Var 0)))))))
            ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0))))))))
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
               ((Var 0)
                (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                 (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType () ((Prod ((Var 0) (Var 1))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Var 0)))))))
                    (Var 0))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                   ((Num (Int I32)))))
                 (Var 0)))))))
           (Plug (Prod ((Atom I32))))))
         (stack ((Plug (Prod ((Atom I32) (Atom I32)))) (Var 0)))))))
     (instr
      (Unpack
       (ValType
        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Var 0))))))
       InferFx
       ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
        (LocalGet 8 Follow) (LocalGet 5 Follow)
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Var 0) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                 (Prod
                  ((CodeRef
                    (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Var 0)))))))
             (Var 0))))))
        (Group 2) (LocalGet 7 Follow) CallIndirect (LocalGet 7 Move) Drop
        (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Var 0))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Var 0)
                         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Var 0)))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Var 0)))))))
                    (Var 0))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
              (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType () ((Prod ((Var 0) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                     (Prod
                      ((CodeRef
                        (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Var 0)))))))
                 (Var 0))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Var 0)
                     (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Var 0)))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Var 0)))))))
                (Var 0)))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Var 0))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0)))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Var 0)
                         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                          (Prod
                           ((CodeRef
                             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Var 0)))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                        (Prod
                         ((CodeRef
                           (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Var 0)))))))
                    (Var 0))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
              (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
               (Prod
                ((CodeRef
                  (FunctionType () ((Prod ((Var 0) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                     (Prod
                      ((CodeRef
                        (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Var 0)))))))
                 (Var 0))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Var 0)
                     (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                      (Prod
                       ((CodeRef
                         (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Var 0)))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Var 0)))))))
                (Var 0)))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                  (Prod
                   ((CodeRef
                     (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Var 0))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
              (Prod
               ((CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Var 0)))))))
          ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
            (Prod
             ((CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Var 0))))))))
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
        ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Var 0)
                 (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) AnyRefs)
                  (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                   (Prod
                    ((CodeRef
                      (FunctionType () ((Prod ((Var 0) (Var 1))))
                       ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                         (Prod
                          ((CodeRef
                            (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                             ((Num (Int I32)))))
                           (Var 0)))))))
                     (Var 0))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Var 0)))))))
            (Var 0)))))))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list[invalid]-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Case
        (1 3
         ((Plug
           (Prod
            ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Ref (Base MM) Mut (Ser (Prod ())))
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
          (Ref (Base MM) Mut (Ser (Prod ())))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
               ((Num (Int I32)))))
             (Var 0))))
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
             (Ref (Base MM) Mut
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))))))))
       InferFx
       (((LocalSet 5) (LocalGet 5 Follow)
         (Inject 0
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM) Mut
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))))))
         (LocalGet 5 Move) Drop)
        ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
         (LocalGet 3 Follow)
         (Unpack (ValType ((Num (Int I32)))) InferFx
          ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
           (LocalGet 11 Follow) (LocalGet 7 Follow) (Group 2)
           (LocalGet 10 Follow) CallIndirect (LocalGet 10 Move) Drop
           (LocalGet 11 Move) Drop (LocalGet 9 Move) Drop))
         (CodeRef 1) (Group 0) (New MM Mut) (Group 2)
         (Pack (Type (Ref (Base MM) Mut (Ser (Prod ()))))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Var 0)
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                    (Prod
                     ((CodeRef
                       (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Var 0))))
                   (Rec
                    (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                     AnyRefs)
                    (Sum
                     ((Prod ())
                      (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0)))))))))))))
              ((Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0)))))))))))
            (Var 0))))
         (Unpack
          (ValType
           ((Rec
             (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
             (Sum
              ((Prod ())
               (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))
          InferFx
          ((LocalSet 12) (LocalGet 12 Follow) Ungroup (LocalSet 14) (LocalSet 13)
           (LocalGet 14 Follow) (LocalGet 3 Follow) (LocalGet 8 Follow)
           (Load (Path ()) Move) (LocalSet 15) Drop (LocalGet 15 Move) (Group 2)
           (Group 2) (LocalGet 13 Follow) CallIndirect (LocalGet 13 Move) Drop
           (LocalGet 14 Move) Drop (LocalGet 12 Move) Drop))
         (New MM Mut) (Group 2)
         (Inject 1
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM) Mut
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))))))
         (LocalGet 7 Move) Drop (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
          (Sum
           ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) Mut (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Var 0))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ())
              (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))
         (FunctionType () ()
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ())
              (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) Mut (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) Mut (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
                (Prod
                 ((CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Var 0))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) AnyRefs)
            (Sum
             ((Prod ())
              (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0))))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug
          (Prod
           ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) Mut (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) AnyRefs))
          (Prod
           ((CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Var 0))))
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
             (Ref (Base MM) Mut
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                 AnyRefs)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) Mut (Ser (Var 0)))))))))))))))))))
    -----------peano_3-----------
    (module
      (func (-> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
        group ;; [] -> [(prod)]
        inject 0 ;; [(prod)] ->
                    [(sum  (prod)
                       (ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        fold ;; [(sum  (prod)
                   (ref (base mm) mut
                     (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
               [(ref (base mm) mut
                  (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        inject 1 ;; [(ref (base mm) mut
                       (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                    ->
                    [(sum  (prod)
                       (ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        fold ;; [(sum  (prod)
                   (ref (base mm) mut
                     (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
               [(ref (base mm) mut
                  (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        inject 1 ;; [(ref (base mm) mut
                       (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                    ->
                    [(sum  (prod)
                       (ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        fold ;; [(sum  (prod)
                   (ref (base mm) mut
                     (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        new ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
               [(ref (base mm) mut
                  (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        inject 1 ;; [(ref (base mm) mut
                       (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                    ->
                    [(sum  (prod)
                       (ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        fold ;; [(sum  (prod)
                   (ref (base mm) mut
                     (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))])
      (table)
      (export "_start" (func 0)))
    -----------peano-----------
    (module
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
          -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))) (local ptr
          (prod (sum (prod) ptr) (sum (prod) ptr)) (sum (prod) ptr) (sum (prod) ptr)
          (prod) ptr (prod i32 ptr) i32 ptr (sum (prod) ptr))
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
        local.set 2 ;; [(prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
        ungroup ;; [(prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
                   ->
                   [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.set 4 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        local.set 3 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        local.get move 3 ;; [] -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        unfold ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                  [(sum  (prod)
                     (ref (base mm) mut
                       (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        case
          (localfx [0 => (plug (prod i32 i32 i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (plug (prod i32 i32 i32 i32))] [3 => (plug (prod i32 i32))]
            [4 => (plug (prod i32 i32))] [5 => (plug (prod))] [6 => (plug (prod i32))]
            [7 => (plug (prod i32 i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32))]
            [10 => (plug (prod i32 i32))])
          (0
            local.set 5 ;; [(prod)] -> []
            local.get move 4 ;; [] ->
                                [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
            local.get move 5 ;; [] -> [(prod)]
            drop ;; [(prod)] -> [])
          (1
            local.set 6 ;; [(ref (base mm) mut
                              (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> []
            coderef 0 ;; [] ->
                         [(coderef
                            ((prod (ref (base mm) mut (ser (prod)))
                               (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
            group ;; [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (ref (base mm) mut (ser (prod)))]
                     ->
                     [(prod
                        (coderef
                          ((prod (ref (base mm) mut (ser (prod)))
                             (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                          -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (ref (base mm) mut (ser (prod))))]
            pack ;; [(prod
                       (coderef
                         ((prod (ref (base mm) mut (ser (prod)))
                            (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                         -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                       (ref (base mm) mut (ser (prod))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                       (prod
                         (coderef
                           ((prod (var 0)
                              (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                           -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                         (var 0)))]
            unpack (localfx [0 => (plug (prod i32 i32 i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                     [2 => (plug (prod i32 i32 i32 i32))] [3 => (plug (prod i32 i32))]
                     [4 => (plug (prod i32 i32))] [5 => (plug (prod))] [6 => (plug (prod i32))]
                     [7 => (plug (prod i32 i32))] [8 => (plug (prod i32))]
                     [9 => (plug (prod i32))] [10 => (plug (prod i32 i32))])
              local.set 7 ;; [(prod
                                (coderef
                                  ((prod (var 0)
                                     (prod
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                  -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                (var 0))]
                             -> []
              local.get move 7 ;; [] ->
                                  [(prod
                                     (coderef
                                       ((prod (var 0)
                                          (prod
                                            (rec (val (sum (prod) ptr) anyrefs)
                                              (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                            (rec (val (sum (prod) ptr) anyrefs)
                                              (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                       ->
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                     (var 0))]
              ungroup ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                              -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            (var 0))]
                         ->
                         [(coderef
                            ((prod (var 0)
                               (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                          (var 0)]
              local.set 9 ;; [(var 0)] -> []
              local.set 8 ;; [(coderef
                                ((prod (var 0)
                                   (prod
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                             -> []
              local.get move 9 ;; [] -> [(var 0)]
              local.get move 6 ;; [] ->
                                  [(ref (base mm) mut
                                     (ser
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
              load (path) move ;; [(ref (base mm) mut
                                     (ser
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                                  ->
                                  [(ref (base mm) mut (span (rep (sum (prod) ptr))))
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              local.set 10 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
              drop ;; [(ref (base mm) mut (span (rep (sum (prod) ptr))))] -> []
              local.get move 10 ;; [] ->
                                   [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              local.get move 4 ;; [] ->
                                  [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              group ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
                       ->
                       [(prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
              group ;; [(var 0)
                        (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
                       ->
                       [(prod (var 0)
                          (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
              local.get copy 8 ;; [] ->
                                  [(coderef
                                     ((prod (var 0)
                                        (prod
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                     ->
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
              call_indirect ;; [(prod (var 0)
                                  (prod
                                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                (coderef
                                  ((prod (var 0)
                                     (prod
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                  -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                               -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              local.get move 8 ;; [] ->
                                  [(coderef
                                     ((prod (var 0)
                                        (prod
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                     ->
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
              drop ;; [(coderef
                         ((prod (var 0)
                            (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                         -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                      -> []
              local.get move 9 ;; [] -> [(plug (prod i32))]
              drop ;; [(plug (prod i32))] -> []
              local.get move 7 ;; [] -> [(plug (prod i32 i32))]
              drop ;; [(plug (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod
                        (coderef
                          ((prod (var 0)
                             (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                          -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (var 0)))]
                   -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
            new ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                   [(ref (base mm) mut
                      (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
            inject 1 ;; [(ref (base mm) mut
                           (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                        ->
                        [(sum  (prod)
                           (ref (base mm) mut
                             (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
            fold ;; [(sum  (prod)
                       (ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                    -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
            local.get move 6 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> [])
        end ;; [(sum  (prod)
                  (ref (base mm) mut
                    (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
               -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.get move 3 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 4 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32 i32 i32))]
        drop ;; [(plug (prod i32 i32 i32 i32))] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))) (local ptr i32
          (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
            [5 => (plug (prod i32))])
          group ;; [] -> [(prod)]
          inject 0 ;; [(prod)] ->
                      [(sum  (prod)
                         (ref (base mm) mut
                           (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        else
          coderef 1 ;; [] ->
                       [(coderef
                          ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef
                      ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod
                      (coderef
                        ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod
                     (coderef
                       ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod
                       (coderef
                         ((prod (var 0) (num i32)) ->
                         (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                       (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
                   [5 => (plug (prod i32))])
            local.set 3 ;; [(prod
                              (coderef
                                ((prod (var 0) (num i32)) ->
                                (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                              (var 0))]
                           -> []
            local.get move 3 ;; [] ->
                                [(prod
                                   (coderef
                                     ((prod (var 0) (num i32)) ->
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                   (var 0))]
            ungroup ;; [(prod
                          (coderef
                            ((prod (var 0) (num i32)) ->
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                          (var 0))]
                       ->
                       [(coderef
                          ((prod (var 0) (num i32)) ->
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (var 0)]
            local.set 5 ;; [(var 0)] -> []
            local.set 4 ;; [(coderef
                              ((prod (var 0) (num i32)) ->
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> []
            local.get move 5 ;; [] -> [(var 0)]
            local.get copy 2 ;; [] -> [(num i32)]
            num_const 1 ;; [] -> [(num i32)]
            i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 4 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (num i32)) ->
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
            call_indirect ;; [(prod (var 0) (num i32))
                              (coderef
                                ((prod (var 0) (num i32)) ->
                                (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                             -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
            local.get move 4 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (num i32)) ->
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
            drop ;; [(coderef
                       ((prod (var 0) (num i32)) ->
                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                    -> []
            local.get move 5 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod
                      (coderef
                        ((prod (var 0) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (var 0)))]
                 -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          new ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                 [(ref (base mm) mut
                    (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          inject 1 ;; [(ref (base mm) mut
                         (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                      ->
                      [(sum  (prod)
                         (ref (base mm) mut
                           (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        end ;; [(num i32)] ->
               [(sum  (prod)
                  (ref (base mm) mut
                    (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        fold ;; [(sum  (prod)
                   (ref (base mm) mut
                     (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
                -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
          -> (num i32)) (local ptr (sum (prod) ptr) (prod) ptr (prod i32 ptr) i32 ptr
          (sum (prod) ptr))
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.set 2 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        unfold ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                  [(sum  (prod)
                     (ref (base mm) mut
                       (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
        case
          (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (plug (prod i32 i32))] [3 => (plug (prod))] [4 => (plug (prod i32))]
            [5 => (plug (prod i32 i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))]
            [8 => (plug (prod i32 i32))])
          (0
            local.set 3 ;; [(prod)] -> []
            num_const 0 ;; [] -> [(num i32)]
            local.get move 3 ;; [] -> [(prod)]
            drop ;; [(prod)] -> [])
          (1
            local.set 4 ;; [(ref (base mm) mut
                              (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> []
            num_const 1 ;; [] -> [(num i32)]
            coderef 2 ;; [] ->
                         [(coderef
                            ((prod (ref (base mm) mut (ser (prod)))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                            -> (num i32)))]
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
            group ;; [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                        -> (num i32)))
                      (ref (base mm) mut (ser (prod)))]
                     ->
                     [(prod
                        (coderef
                          ((prod (ref (base mm) mut (ser (prod)))
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                          -> (num i32)))
                        (ref (base mm) mut (ser (prod))))]
            pack ;; [(prod
                       (coderef
                         ((prod (ref (base mm) mut (ser (prod)))
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                         -> (num i32)))
                       (ref (base mm) mut (ser (prod))))]
                    ->
                    [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                       (prod
                         (coderef
                           ((prod (var 0)
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                           -> (num i32)))
                         (var 0)))]
            unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                     [2 => (plug (prod i32 i32))] [3 => (plug (prod))] [4 => (plug (prod i32))]
                     [5 => (plug (prod i32 i32))] [6 => (plug (prod i32))]
                     [7 => (plug (prod i32))] [8 => (plug (prod i32 i32))])
              local.set 5 ;; [(prod
                                (coderef
                                  ((prod (var 0)
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                  -> (num i32)))
                                (var 0))]
                             -> []
              local.get move 5 ;; [] ->
                                  [(prod
                                     (coderef
                                       ((prod (var 0)
                                          (rec (val (sum (prod) ptr) anyrefs)
                                            (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                       -> (num i32)))
                                     (var 0))]
              ungroup ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                              -> (num i32)))
                            (var 0))]
                         ->
                         [(coderef
                            ((prod (var 0)
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                            -> (num i32)))
                          (var 0)]
              local.set 7 ;; [(var 0)] -> []
              local.set 6 ;; [(coderef
                                ((prod (var 0)
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                -> (num i32)))]
                             -> []
              local.get move 7 ;; [] -> [(var 0)]
              local.get move 4 ;; [] ->
                                  [(ref (base mm) mut
                                     (ser
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
              load (path) move ;; [(ref (base mm) mut
                                     (ser
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                                  ->
                                  [(ref (base mm) mut (span (rep (sum (prod) ptr))))
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              local.set 8 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
              drop ;; [(ref (base mm) mut (span (rep (sum (prod) ptr))))] -> []
              local.get move 8 ;; [] ->
                                  [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
              group ;; [(var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                       [(prod (var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
              local.get copy 6 ;; [] ->
                                  [(coderef
                                     ((prod (var 0)
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                     -> (num i32)))]
              call_indirect ;; [(prod (var 0)
                                  (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                (coderef
                                  ((prod (var 0)
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                  -> (num i32)))]
                               -> [(num i32)]
              local.get move 6 ;; [] ->
                                  [(coderef
                                     ((prod (var 0)
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                     -> (num i32)))]
              drop ;; [(coderef
                         ((prod (var 0)
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                         -> (num i32)))]
                      -> []
              local.get move 7 ;; [] -> [(plug (prod i32))]
              drop ;; [(plug (prod i32))] -> []
              local.get move 5 ;; [] -> [(plug (prod i32 i32))]
              drop ;; [(plug (prod i32 i32))] -> []
            end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod
                        (coderef
                          ((prod (var 0)
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                          -> (num i32)))
                        (var 0)))]
                   -> [(num i32)]
            i32.add ;; [(num i32) (num i32)] -> [(num i32)]
            local.get move 4 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> [])
        end ;; [(sum  (prod)
                  (ref (base mm) mut
                    (ser (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))))]
               -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr (sum (prod) ptr)
          (prod i32 ptr) i32 ptr (sum (prod) ptr) (prod i32 ptr) i32 ptr
          (sum (prod) ptr) (prod i32 ptr) i32 ptr)
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0) (num i32)) ->
                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32 i32))]
                 [8 => (plug (prod i32 i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))]
                 [11 => (plug (prod i32 i32))] [12 => (plug (prod i32 i32))]
                 [13 => (plug (prod i32))] [14 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0) (num i32)) ->
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0) (num i32)) ->
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0) (num i32)) ->
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          num_const 6 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          call_indirect ;; [(prod (var 0) (num i32))
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          drop ;; [(coderef
                     ((prod (var 0) (num i32)) ->
                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0) (num i32)) ->
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (var 0)))]
               -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.set 3 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0) (num i32)) ->
                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))]
                 [3 => (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
                 [4 => (plug (prod i32 i32))] [5 => (plug (prod i32))] [6 => (plug (prod i32))]
                 [7 => (plug (prod i32 i32))] [8 => (plug (prod i32 i32))]
                 [9 => (plug (prod i32))] [10 => (plug (prod i32))] [11 => (plug (prod i32 i32))]
                 [12 => (plug (prod i32 i32))] [13 => (plug (prod i32))]
                 [14 => (plug (prod i32))])
          local.set 4 ;; [(prod
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            (var 0))]
                         -> []
          local.get move 4 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0) (num i32)) ->
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0) (num i32)) ->
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0) (num i32)) ->
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.set 5 ;; [(coderef
                            ((prod (var 0) (num i32)) ->
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                         -> []
          local.get move 6 ;; [] -> [(var 0)]
          num_const 7 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 5 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          call_indirect ;; [(prod (var 0) (num i32))
                            (coderef
                              ((prod (var 0) (num i32)) ->
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          local.get move 5 ;; [] ->
                              [(coderef
                                 ((prod (var 0) (num i32)) ->
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          drop ;; [(coderef
                     ((prod (var 0) (num i32)) ->
                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                  -> []
          local.get move 6 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 4 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0) (num i32)) ->
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (var 0)))]
               -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.set 7 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        coderef 0 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                         (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                           (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0)
                          (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                            (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                       -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32 i32))]
                 [8 => (plug (prod i32 i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))]
                 [11 => (plug (prod i32 i32))] [12 => (plug (prod i32 i32))]
                 [13 => (plug (prod i32))] [14 => (plug (prod i32))])
          local.set 8 ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                              -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            (var 0))]
                         -> []
          local.get move 8 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0)
                                      (prod
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                        (rec (val (sum (prod) ptr) anyrefs)
                                          (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                   -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                               (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                          -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                        -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      (var 0)]
          local.set 10 ;; [(var 0)] -> []
          local.set 9 ;; [(coderef
                            ((prod (var 0)
                               (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                         -> []
          local.get move 10 ;; [] -> [(var 0)]
          local.get move 3 ;; [] -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          local.get move 7 ;; [] -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          group ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                    (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
                   ->
                   [(prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
          group ;; [(var 0)
                    (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
                   ->
                   [(prod (var 0)
                      (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          local.get copy 9 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                 -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          call_indirect ;; [(prod (var 0)
                              (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                            (coderef
                              ((prod (var 0)
                                 (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                   (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                              -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                           -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          local.get move 9 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                                      (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                                 -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
          drop ;; [(coderef
                     ((prod (var 0)
                        (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                          (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                     -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))]
                  -> []
          local.get move 10 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 8 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0)
                         (prod (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))
                           (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                      -> (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))))
                    (var 0)))]
               -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
        local.set 11 ;; [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] -> []
        coderef 2 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                        -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                    -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                      -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                     -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                       -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32 i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32 i32))]
                 [8 => (plug (prod i32 i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))]
                 [11 => (plug (prod i32 i32))] [12 => (plug (prod i32 i32))]
                 [13 => (plug (prod i32))] [14 => (plug (prod i32))])
          local.set 12 ;; [(prod
                             (coderef
                               ((prod (var 0)
                                  (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                               -> (num i32)))
                             (var 0))]
                          -> []
          local.get move 12 ;; [] ->
                               [(prod
                                  (coderef
                                    ((prod (var 0)
                                       (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                    -> (num i32)))
                                  (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                          -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                        -> (num i32)))
                      (var 0)]
          local.set 14 ;; [(var 0)] -> []
          local.set 13 ;; [(coderef
                             ((prod (var 0)
                                (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                             -> (num i32)))]
                          -> []
          local.get move 14 ;; [] -> [(var 0)]
          local.get move 11 ;; [] -> [(rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))]
          group ;; [(var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0)))))] ->
                   [(prod (var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))]
          local.get copy 13 ;; [] ->
                               [(coderef
                                  ((prod (var 0)
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                  -> (num i32)))]
          call_indirect ;; [(prod (var 0)
                              (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                            (coderef
                              ((prod (var 0)
                                 (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                              -> (num i32)))]
                           -> [(num i32)]
          local.get move 13 ;; [] ->
                               [(coderef
                                  ((prod (var 0)
                                     (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                                  -> (num i32)))]
          drop ;; [(coderef
                     ((prod (var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                     -> (num i32)))]
                  -> []
          local.get move 14 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 12 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0) (rec (val (sum (prod) ptr) anyrefs) (sum  (prod) (ref (base mm) mut (ser (var 0))))))
                      -> (num i32)))
                    (var 0)))]
               -> [(num i32)]
        local.get move 11 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 7 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 3 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (table 0 1 2)
      (export "_start" (func 3)))
    -----------mini_zip-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func ((prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))) -> (prod (num i32) (num i32))) (local ptr
          (prod i32 i32) i32 i32 (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (prod (num i32) (num i32)))] ->
                   [(ref (base mm) mut (ser (prod))) (prod (num i32) (num i32))]
        local.set 2 ;; [(prod (num i32) (num i32))] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(prod (num i32) (num i32))]
        ungroup ;; [(prod (num i32) (num i32))] -> [(num i32) (num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.set 3 ;; [(num i32)] -> []
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (prod (num i32) (num i32))] [3 => (num i32)] [4 => (num i32)]
                 [5 => (plug (prod i32 i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))]
                 [8 => (plug (prod i32 i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))])
          local.set 5 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 5 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 7 ;; [(var 0)] -> []
          local.set 6 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 7 ;; [] -> [(var 0)]
          local.get copy 3 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 6 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 6 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 7 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 5 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (prod (num i32) (num i32))] [3 => (num i32)] [4 => (num i32)]
                 [5 => (plug (prod i32 i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))]
                 [8 => (plug (prod i32 i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))])
          local.set 8 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 8 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 10 ;; [(var 0)] -> []
          local.set 9 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 10 ;; [] -> [(var 0)]
          local.get copy 4 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 9 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 9 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 10 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 8 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        group ;; [(num i32) (num i32)] -> [(prod (num i32) (num i32))]
        local.get move 3 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(prod (num i32) (num i32))]
        drop ;; [(prod (num i32) (num i32))] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (prod (ref (base mm) mut (ser (num i32))) (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))))
          -> (ref (base mm) mut (ser (prod (num i32) (ref (base mm) mut (ser (num i32))))))) (local ptr
          (prod ptr ptr) ptr ptr i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (prod (ref (base mm) mut (ser (num i32)))
                                 (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (prod (ref (base mm) mut (ser (num i32)))
                        (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (prod (ref (base mm) mut (ser (num i32)))
                      (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32))))))]
        local.set 2 ;; [(prod (ref (base mm) mut (ser (num i32)))
                          (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32))))))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(prod (ref (base mm) mut (ser (num i32)))
                               (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32))))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (num i32)))
                      (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32))))))]
                   -> [(ref (base mm) mut (ser (num i32))) (ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))]
        local.set 4 ;; [(ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))] -> []
        local.set 3 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.get move 3 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        load (path) move ;; [(ref (base mm) mut (ser (num i32)))] -> [(ref (base mm) mut (span (rep i32))) (num i32)]
        local.set 5 ;; [(num i32)] -> []
        drop ;; [(ref (base mm) mut (span (rep i32)))] -> []
        local.get move 5 ;; [] -> [(num i32)]
        local.get move 4 ;; [] -> [(ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))]
        load (path) move ;; [(ref (base mm) mut (ser (ref (base mm) mut (ser (num i32)))))] ->
                            [(ref (base mm) mut (span (rep ptr))) (ref (base mm) mut (ser (num i32)))]
        local.set 6 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        drop ;; [(ref (base mm) mut (span (rep ptr)))] -> []
        local.get move 6 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        group ;; [(num i32) (ref (base mm) mut (ser (num i32)))] -> [(prod (num i32) (ref (base mm) mut (ser (num i32))))]
        new ;; [(prod (num i32) (ref (base mm) mut (ser (num i32))))] ->
               [(ref (base mm) mut (ser (prod (num i32) (ref (base mm) mut (ser (num i32))))))]
        local.get move 3 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 4 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (table 0 1 2)
      (export "typle_add1" (func 1)))
    -----------apply_hof-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod) i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        load (path) move ;; [(ref (base mm) mut (ser (prod)))] -> [(ref (base mm) mut (span (rep (prod)))) (prod)]
        local.set 3 ;; [(prod)] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod))))] -> []
        local.get move 3 ;; [] -> [(prod)]
        ungroup ;; [(prod)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        num_const 5 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (prod
               (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                 (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
               (num i32)))
          -> (num i32)) (local ptr (prod (prod i32 ptr) i32) (prod i32 ptr) i32
          (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (prod
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (num i32)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (prod
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (num i32)))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
        local.set 2 ;; [(prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(prod
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (num i32))]
        ungroup ;; [(prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
                   ->
                   [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.set 3 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (plug (prod i32 i32 i32))] [3 => (plug (prod i32 i32))]
                 [4 => (num i32)] [5 => (plug (prod i32 i32))] [6 => (plug (prod i32))]
                 [7 => (plug (prod i32))])
          local.set 5 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 5 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 7 ;; [(var 0)] -> []
          local.set 6 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 7 ;; [] -> [(var 0)]
          local.get copy 4 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 6 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 6 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 7 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 5 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 3 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32 i32))]
        drop ;; [(plug (prod i32 i32 i32))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (prod
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (num i32)))
                        -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (prod
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                         (num i32)))
                    -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (prod
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (num i32)))
                      -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32)))
                     -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0)
                          (prod
                            (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                            (num i32)))
                       -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (prod
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (num i32)))
                              -> (num i32)))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0)
                                      (prod
                                        (exists.type (val (prod i32 ptr) anyrefs)
                                          (val ptr anyrefs)
                                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                        (num i32)))
                                   -> (num i32)))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (prod
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (num i32)))
                          -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (prod
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (num i32)))
                        -> (num i32)))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0)
                               (prod
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (num i32)))
                            -> (num i32)))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          num_const 10 ;; [] -> [(num i32)]
          group ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (num i32)]
                   ->
                   [(prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
          group ;; [(var 0)
                    (prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
                   ->
                   [(prod (var 0)
                      (prod
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (num i32)))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (num i32)))
                                 -> (num i32)))]
          call_indirect ;; [(prod (var 0)
                              (prod
                                (exists.type (val (prod i32 ptr) anyrefs)
                                  (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                (num i32)))
                            (coderef
                              ((prod (var 0)
                                 (prod
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (num i32)))
                              -> (num i32)))]
                           -> [(num i32)]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (num i32)))
                                 -> (num i32)))]
          drop ;; [(coderef
                     ((prod (var 0)
                        (prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32)))
                     -> (num i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0)
                         (prod
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (num i32)))
                      -> (num i32)))
                    (var 0)))]
               -> [(num i32)])
      (table 0 1)
      (export "_start" (func 2)))
    -----------compose_hof-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod) i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        load (path) move ;; [(ref (base mm) mut (ser (prod)))] -> [(ref (base mm) mut (span (rep (prod)))) (prod)]
        local.set 3 ;; [(prod)] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod))))] -> []
        local.get move 3 ;; [] -> [(prod)]
        ungroup ;; [(prod)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod) i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        load (path) move ;; [(ref (base mm) mut (ser (prod)))] -> [(ref (base mm) mut (span (rep (prod)))) (prod)]
        local.set 3 ;; [(prod)] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod))))] -> []
        local.get move 3 ;; [] -> [(prod)]
        ungroup ;; [(prod)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 4 ;; [] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        i32.mul ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (prod
               (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                 (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
               (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                 (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
               (num i32)))
          -> (num i32)) (local ptr (prod (prod i32 ptr) (prod i32 ptr) i32)
          (prod i32 ptr) (prod i32 ptr) i32 (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (prod
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (num i32)))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (prod
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (num i32)))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
        local.set 2 ;; [(prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(prod
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (num i32))]
        ungroup ;; [(prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
                   ->
                   [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (num i32)]
        local.set 5 ;; [(num i32)] -> []
        local.set 4 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.set 3 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32 i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (plug (prod i32 i32 i32 i32 i32))] [3 => (plug (prod i32 i32))]
                 [4 => (plug (prod i32 i32))] [5 => (num i32)] [6 => (plug (prod i32 i32))]
                 [7 => (plug (prod i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32 i32))]
                 [10 => (plug (prod i32))] [11 => (plug (prod i32))])
          local.set 6 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 6 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 8 ;; [(var 0)] -> []
          local.set 7 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 8 ;; [] -> [(var 0)]
          local.get move 4 ;; [] ->
                              [(exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32 i32 i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (plug (prod i32 i32 i32 i32 i32))] [3 => (plug (prod i32 i32))]
                   [4 => (plug (prod i32 i32))] [5 => (num i32)] [6 => (plug (prod i32 i32))]
                   [7 => (coderef ((prod (var 0) (num i32)) -> (num i32)))]
                   [8 => (plug (prod i32))] [9 => (plug (prod i32 i32))]
                   [10 => (plug (prod i32))] [11 => (plug (prod i32))])
            local.set 9 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
            local.get move 9 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
            ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                       [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
            local.set 11 ;; [(var 0)] -> []
            local.set 10 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 11 ;; [] -> [(var 0)]
            local.get copy 5 ;; [] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 10 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
            local.get move 10 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 11 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 9 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                 -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 7 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 7 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 8 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 6 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 3 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 4 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 5 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32 i32 i32 i32))]
        drop ;; [(plug (prod i32 i32 i32 i32 i32))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 2 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (prod
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (num i32)))
                        -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (prod
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                         (num i32)))
                    -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (prod
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (num i32)))
                      -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32)))
                     -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0)
                          (prod
                            (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                            (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                            (num i32)))
                       -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (prod
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (num i32)))
                              -> (num i32)))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0)
                                      (prod
                                        (exists.type (val (prod i32 ptr) anyrefs)
                                          (val ptr anyrefs)
                                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                        (exists.type (val (prod i32 ptr) anyrefs)
                                          (val ptr anyrefs)
                                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                        (num i32)))
                                   -> (num i32)))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (prod
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                               (num i32)))
                          -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (prod
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                             (num i32)))
                        -> (num i32)))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0)
                               (prod
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                 (num i32)))
                            -> (num i32)))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          coderef 1 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          num_const 5 ;; [] -> [(num i32)]
          group ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                    (num i32)]
                   ->
                   [(prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
          group ;; [(var 0)
                    (prod
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                      (num i32))]
                   ->
                   [(prod (var 0)
                      (prod
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                        (num i32)))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (num i32)))
                                 -> (num i32)))]
          call_indirect ;; [(prod (var 0)
                              (prod
                                (exists.type (val (prod i32 ptr) anyrefs)
                                  (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                (exists.type (val (prod i32 ptr) anyrefs)
                                  (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                (num i32)))
                            (coderef
                              ((prod (var 0)
                                 (prod
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                   (num i32)))
                              -> (num i32)))]
                           -> [(num i32)]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (prod
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                                      (num i32)))
                                 -> (num i32)))]
          drop ;; [(coderef
                     ((prod (var 0)
                        (prod
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                          (num i32)))
                     -> (num i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0)
                         (prod
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))
                           (num i32)))
                      -> (num i32)))
                    (var 0)))]
               -> [(num i32)])
      (table 0 1 2)
      (export "_start" (func 3)))
    -----------mk_adder_apply_to-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)) (local ptr i32 (prod i32) i32 i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod (num i32)))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod (num i32)))) (num i32))] ->
                   [(ref (base mm) mut (ser (prod (num i32)))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod (num i32))))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod (num i32))))]
        load (path) move ;; [(ref (base mm) mut (ser (prod (num i32))))] ->
                            [(ref (base mm) mut (span (rep (prod i32)))) (prod (num i32))]
        local.set 3 ;; [(prod (num i32))] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod i32))))] -> []
        local.get move 3 ;; [] -> [(prod (num i32))]
        ungroup ;; [(prod (num i32))] -> [(num i32)]
        local.set 4 ;; [(num i32)] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        local.set 5 ;; [(num i32)] -> []
        local.get copy 5 ;; [] -> [(num i32)]
        local.get copy 4 ;; [] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        local.get move 5 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 4 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
          (local ptr i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))]
        local.get copy 2 ;; [] -> [(num i32)]
        group ;; [(num i32)] -> [(prod (num i32))]
        new ;; [(prod (num i32))] -> [(ref (base mm) mut (ser (prod (num i32))))]
        group ;; [(coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                  (ref (base mm) mut (ser (prod (num i32))))]
                 ->
                 [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod (num i32)))))]
        pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod (num i32)))) (num i32)) -> (num i32)))
                   (ref (base mm) mut (ser (prod (num i32)))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
          -> (num i32)) (local ptr (prod i32 ptr) (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        local.set 2 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (plug (prod i32 i32))] [3 => (plug (prod i32 i32))]
                 [4 => (plug (prod i32))] [5 => (plug (prod i32))])
          local.set 3 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 3 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 5 ;; [(var 0)] -> []
          local.set 4 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 5 ;; [] -> [(var 0)]
          num_const 100 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 5 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 3 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr)
        coderef 2 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                        -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                         (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                    -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                      -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                     -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0)
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                       -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                              -> (num i32)))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0)
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                   -> (num i32)))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                          -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                        -> (num i32)))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0)
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                            -> (num i32)))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          coderef 1 ;; [] ->
                       [(coderef
                          ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef
                      ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod
                      (coderef
                        ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod
                     (coderef
                       ((prod (ref (base mm) mut (ser (prod))) (num i32)) ->
                       (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                         (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod
                       (coderef
                         ((prod (var 0) (num i32)) ->
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                       (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32))]
                   [1 =>
                   (coderef
                     ((prod (var 0)
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                     -> (num i32)))]
                   [2 => (plug (prod i32))] [3 => (plug (prod i32 i32))]
                   [4 => (plug (prod i32))] [5 => (plug (prod i32))])
            local.set 3 ;; [(prod
                              (coderef
                                ((prod (var 0) (num i32)) ->
                                (exists.type (val (prod i32 ptr) anyrefs)
                                  (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                              (var 0))]
                           -> []
            local.get move 3 ;; [] ->
                                [(prod
                                   (coderef
                                     ((prod (var 0) (num i32)) ->
                                     (exists.type (val (prod i32 ptr) anyrefs)
                                       (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                                   (var 0))]
            ungroup ;; [(prod
                          (coderef
                            ((prod (var 0) (num i32)) ->
                            (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                              (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                          (var 0))]
                       ->
                       [(coderef
                          ((prod (var 0) (num i32)) ->
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                        (var 0)]
            local.set 5 ;; [(var 0)] -> []
            local.set 4 ;; [(coderef
                              ((prod (var 0) (num i32)) ->
                              (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                           -> []
            local.get move 5 ;; [] -> [(var 0)]
            num_const 7 ;; [] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 4 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (num i32)) ->
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
            call_indirect ;; [(prod (var 0) (num i32))
                              (coderef
                                ((prod (var 0) (num i32)) ->
                                (exists.type (val (prod i32 ptr) anyrefs)
                                  (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                             ->
                             [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
            local.get move 4 ;; [] ->
                                [(coderef
                                   ((prod (var 0) (num i32)) ->
                                   (exists.type (val (prod i32 ptr) anyrefs)
                                     (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
            drop ;; [(coderef
                       ((prod (var 0) (num i32)) ->
                       (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                         (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))]
                    -> []
            local.get move 5 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod
                      (coderef
                        ((prod (var 0) (num i32)) ->
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))))
                      (var 0)))]
                 ->
                 [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          group ;; [(var 0)
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                   ->
                   [(prod (var 0)
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (exists.type (val (prod i32 ptr) anyrefs)
                                      (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                 -> (num i32)))]
          call_indirect ;; [(prod (var 0)
                              (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                            (coderef
                              ((prod (var 0)
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                              -> (num i32)))]
                           -> [(num i32)]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (exists.type (val (prod i32 ptr) anyrefs)
                                      (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                 -> (num i32)))]
          drop ;; [(coderef
                     ((prod (var 0)
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                     -> (num i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0)
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                      -> (num i32)))
                    (var 0)))]
               -> [(num i32)])
      (table 0 1 2)
      (export "_start" (func 3)))
    -----------closure_with_ref-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)) -> (num i32)) (local ptr
          (prod) (prod ptr) ptr (prod) i32)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod))] ->
                   [(ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)]
        local.set 2 ;; [(prod)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32))))))] -> []
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32))))))]
        load (path) move ;; [(ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32))))))] ->
                            [(ref (base mm) mut (span (rep (prod ptr)))) (prod (ref (base mm) mut (ser (num i32))))]
        local.set 3 ;; [(prod (ref (base mm) mut (ser (num i32))))] -> []
        drop ;; [(ref (base mm) mut (span (rep (prod ptr))))] -> []
        local.get move 3 ;; [] -> [(prod (ref (base mm) mut (ser (num i32))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (num i32))))] -> [(ref (base mm) mut (ser (num i32)))]
        local.set 4 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        local.get copy 2 ;; [] -> [(prod)]
        local.set 5 ;; [(prod)] -> []
        local.get move 4 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        load (path) move ;; [(ref (base mm) mut (ser (num i32)))] -> [(ref (base mm) mut (span (rep i32))) (num i32)]
        local.set 6 ;; [(num i32)] -> []
        drop ;; [(ref (base mm) mut (span (rep i32)))] -> []
        local.get move 6 ;; [] -> [(num i32)]
        local.get move 5 ;; [] -> [(prod)]
        drop ;; [(prod)] -> []
        local.get move 4 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 1 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 2 ;; [] -> [(prod)]
        drop ;; [(prod)] -> [])
      (func (-> (num i32)) (local ptr (prod i32 ptr) (prod i32 ptr) i32 ptr)
        num_const 42 ;; [] -> [(num i32)]
        new ;; [(num i32)] -> [(ref (base mm) mut (ser (num i32)))]
        local.set 0 ;; [(ref (base mm) mut (ser (num i32)))] -> []
        coderef 0 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)) -> (num i32)))]
        local.get move 0 ;; [] -> [(ref (base mm) mut (ser (num i32)))]
        group ;; [(ref (base mm) mut (ser (num i32)))] -> [(prod (ref (base mm) mut (ser (num i32))))]
        new ;; [(prod (ref (base mm) mut (ser (num i32))))] ->
               [(ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32))))))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)) -> (num i32)))
                  (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32))))))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)) -> (num i32)))
                    (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))) (prod)) -> (num i32)))
                   (ref (base mm) mut (ser (prod (ref (base mm) mut (ser (num i32)))))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
        local.set 1 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
                       -> []
        local.get move 1 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32))] [1 => (plug (prod i32 i32))]
                 [2 => (plug (prod i32 i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))])
          local.set 2 ;; [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))] -> []
          local.get move 2 ;; [] -> [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.set 3 ;; [(coderef ((prod (var 0) (prod)) -> (num i32)))] -> []
          local.get move 4 ;; [] -> [(var 0)]
          group ;; [] -> [(prod)]
          group ;; [(var 0) (prod)] -> [(prod (var 0) (prod))]
          local.get copy 3 ;; [] -> [(coderef ((prod (var 0) (prod)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (prod)) (coderef ((prod (var 0) (prod)) -> (num i32)))] -> [(num i32)]
          local.get move 3 ;; [] -> [(coderef ((prod (var 0) (prod)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (prod)) -> (num i32)))] -> []
          local.get move 4 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 2 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (prod)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 1 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> []
        local.get move 0 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> [])
      (table 0)
      (export "_start" (func 1)))
    -----------factorial_hof-----------
    (module
      (func ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)) (local ptr i32 (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] -> [(prod (ref (base mm) mut (ser (prod))) (num i32))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod))) (num i32))] -> [(ref (base mm) mut (ser (prod))) (num i32)]
        local.set 2 ;; [(num i32)] -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get copy 2 ;; [] -> [(num i32)]
        i32.eqz ;; [(num i32)] -> [(num i32)]
        if
          (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
            [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
            [5 => (plug (prod i32))])
          num_const 1 ;; [] -> [(num i32)]
        else
          local.get copy 2 ;; [] -> [(num i32)]
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          unpack (localfx [0 => (plug (prod i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                   [2 => (num i32)] [3 => (plug (prod i32 i32))] [4 => (plug (prod i32))]
                   [5 => (plug (prod i32))])
            local.set 3 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
            local.get move 3 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
            ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                       [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
            local.set 5 ;; [(var 0)] -> []
            local.set 4 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 5 ;; [] -> [(var 0)]
            local.get copy 2 ;; [] -> [(num i32)]
            num_const 1 ;; [] -> [(num i32)]
            i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
            group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
            local.get copy 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
            local.get move 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
            drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
            local.get move 5 ;; [] -> [(plug (prod i32))]
            drop ;; [(plug (prod i32))] -> []
            local.get move 3 ;; [] -> [(plug (prod i32 i32))]
            drop ;; [(plug (prod i32 i32))] -> []
          end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                    (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                 -> [(num i32)]
          i32.mul ;; [(num i32) (num i32)] -> [(num i32)]
        end ;; [(num i32)] -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(num i32)]
        drop ;; [(num i32)] -> [])
      (func
          ((prod (ref (base mm) mut (ser (prod)))
             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
          -> (num i32)) (local ptr (prod i32 ptr) (prod i32 ptr) i32 ptr)
        local.get move 0 ;; [] ->
                            [(prod (ref (base mm) mut (ser (prod)))
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
        ungroup ;; [(prod (ref (base mm) mut (ser (prod)))
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
                   ->
                   [(ref (base mm) mut (ser (prod)))
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        local.set 2 ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                       -> []
        local.set 1 ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32 i32))] [1 => (ref (base mm) mut (ser (prod)))]
                 [2 => (plug (prod i32 i32))] [3 => (plug (prod i32 i32))]
                 [4 => (plug (prod i32))] [5 => (plug (prod i32))])
          local.set 3 ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] -> []
          local.get move 3 ;; [] -> [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))]
          ungroup ;; [(prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))] ->
                     [(coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)]
          local.set 5 ;; [(var 0)] -> []
          local.set 4 ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 5 ;; [] -> [(var 0)]
          num_const 6 ;; [] -> [(num i32)]
          group ;; [(var 0) (num i32)] -> [(prod (var 0) (num i32))]
          local.get copy 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          call_indirect ;; [(prod (var 0) (num i32)) (coderef ((prod (var 0) (num i32)) -> (num i32)))] -> [(num i32)]
          local.get move 4 ;; [] -> [(coderef ((prod (var 0) (num i32)) -> (num i32)))]
          drop ;; [(coderef ((prod (var 0) (num i32)) -> (num i32)))] -> []
          local.get move 5 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 3 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
               -> [(num i32)]
        local.get move 1 ;; [] -> [(ref (base mm) mut (ser (prod)))]
        drop ;; [(ref (base mm) mut (ser (prod)))] -> []
        local.get move 2 ;; [] -> [(plug (prod i32 i32))]
        drop ;; [(plug (prod i32 i32))] -> [])
      (func (-> (num i32)) (local (prod i32 ptr) i32 ptr)
        coderef 1 ;; [] ->
                     [(coderef
                        ((prod (ref (base mm) mut (ser (prod)))
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                        -> (num i32)))]
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
        group ;; [(coderef
                    ((prod (ref (base mm) mut (ser (prod)))
                       (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                         (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                    -> (num i32)))
                  (ref (base mm) mut (ser (prod)))]
                 ->
                 [(prod
                    (coderef
                      ((prod (ref (base mm) mut (ser (prod)))
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                      -> (num i32)))
                    (ref (base mm) mut (ser (prod))))]
        pack ;; [(prod
                   (coderef
                     ((prod (ref (base mm) mut (ser (prod)))
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                     -> (num i32)))
                   (ref (base mm) mut (ser (prod))))]
                ->
                [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                   (prod
                     (coderef
                       ((prod (var 0)
                          (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                            (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                       -> (num i32)))
                     (var 0)))]
        unpack (localfx [0 => (plug (prod i32 i32))] [1 => (plug (prod i32))] [2 => (plug (prod i32))])
          local.set 0 ;; [(prod
                            (coderef
                              ((prod (var 0)
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                              -> (num i32)))
                            (var 0))]
                         -> []
          local.get move 0 ;; [] ->
                              [(prod
                                 (coderef
                                   ((prod (var 0)
                                      (exists.type (val (prod i32 ptr) anyrefs)
                                        (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                   -> (num i32)))
                                 (var 0))]
          ungroup ;; [(prod
                        (coderef
                          ((prod (var 0)
                             (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                               (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                          -> (num i32)))
                        (var 0))]
                     ->
                     [(coderef
                        ((prod (var 0)
                           (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                             (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                        -> (num i32)))
                      (var 0)]
          local.set 2 ;; [(var 0)] -> []
          local.set 1 ;; [(coderef
                            ((prod (var 0)
                               (exists.type (val (prod i32 ptr) anyrefs)
                                 (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                            -> (num i32)))]
                         -> []
          local.get move 2 ;; [] -> [(var 0)]
          coderef 0 ;; [] -> [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base mm) mut (ser (prod)))]
          group ;; [(coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                    (ref (base mm) mut (ser (prod)))]
                   ->
                   [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                      (ref (base mm) mut (ser (prod))))]
          pack ;; [(prod (coderef ((prod (ref (base mm) mut (ser (prod))) (num i32)) -> (num i32)))
                     (ref (base mm) mut (ser (prod))))]
                  ->
                  [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                     (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
          group ;; [(var 0)
                    (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                      (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0)))]
                   ->
                   [(prod (var 0)
                      (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                        (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))]
          local.get copy 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (exists.type (val (prod i32 ptr) anyrefs)
                                      (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                 -> (num i32)))]
          call_indirect ;; [(prod (var 0)
                              (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                                (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                            (coderef
                              ((prod (var 0)
                                 (exists.type (val (prod i32 ptr) anyrefs)
                                   (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                              -> (num i32)))]
                           -> [(num i32)]
          local.get move 1 ;; [] ->
                              [(coderef
                                 ((prod (var 0)
                                    (exists.type (val (prod i32 ptr) anyrefs)
                                      (val ptr anyrefs) (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                                 -> (num i32)))]
          drop ;; [(coderef
                     ((prod (var 0)
                        (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                          (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                     -> (num i32)))]
                  -> []
          local.get move 2 ;; [] -> [(plug (prod i32))]
          drop ;; [(plug (prod i32))] -> []
          local.get move 0 ;; [] -> [(plug (prod i32 i32))]
          drop ;; [(plug (prod i32 i32))] -> []
        end ;; [(exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                  (prod
                    (coderef
                      ((prod (var 0)
                         (exists.type (val (prod i32 ptr) anyrefs) (val ptr anyrefs)
                           (prod (coderef ((prod (var 0) (num i32)) -> (num i32))) (var 0))))
                      -> (num i32)))
                    (var 0)))]
               -> [(num i32)])
      (table 0 1)
      (export "_start" (func 2))) |xxx}]
