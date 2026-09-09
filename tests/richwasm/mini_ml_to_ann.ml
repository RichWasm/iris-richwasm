open! Core
open! Stdlib.Format
open! Test_support
open Richwasm_support.Pipeline
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let syntax_pipeline x = ml_pipeline x |> elab_pipeline
  let string_pipeline s = ml_str_pipeline s |> elab_pipeline
  let examples = Test_examples.Mini_ml.all
  let pp = AnnRichWasm.Module.pp
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {xxx|
    -----------one-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (ref (base gc) imm (struct (ser i31) (ser i31) (ser i31) (ser i31))))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 3 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 4 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31 i31 i31] -> [(prod i31 i31 i31 i31)]
        new ;; [(prod i31 i31 i31 i31)] -> [(ref (base gc) imm (ser (prod i31 i31 i31 i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31 i31 i31 i31)))] ->
                [(ref (base gc) imm (struct (ser i31) (ser i31) (ser i31) (ser i31)))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_nested-----------
    (module
      (func
          ((ref (base gc) imm (struct)) ->
          (ref (base gc) imm
            (struct (ser (ref (base gc) imm (struct (ser i31) (ser i31))))
              (ser (ref (base gc) imm (struct (ser i31) (ser i31)))))))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        new ;; [(prod i31 i31)] -> [(ref (base gc) imm (ser (prod i31 i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31 i31)))] -> [(ref (base gc) imm (struct (ser i31) (ser i31)))]
        num_const 3 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 4 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        new ;; [(prod i31 i31)] -> [(ref (base gc) imm (ser (prod i31 i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31 i31)))] -> [(ref (base gc) imm (struct (ser i31) (ser i31)))]
        group ;; [(ref (base gc) imm (struct (ser i31) (ser i31))) (ref (base gc) imm (struct (ser i31) (ser i31)))] ->
                 [(prod (ref (base gc) imm (struct (ser i31) (ser i31))) (ref (base gc) imm (struct (ser i31) (ser i31))))]
        new ;; [(prod (ref (base gc) imm (struct (ser i31) (ser i31))) (ref (base gc) imm (struct (ser i31) (ser i31))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct (ser i31) (ser i31)))
                      (ref (base gc) imm (struct (ser i31) (ser i31))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct (ser i31) (ser i31)))
                       (ref (base gc) imm (struct (ser i31) (ser i31))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct (ser i31) (ser i31))))
                     (ser (ref (base gc) imm (struct (ser i31) (ser i31))))))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_project-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr)
        num_const 42 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 7 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        new ;; [(prod i31 i31)] -> [(ref (base gc) imm (ser (prod i31 i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31 i31)))] -> [(ref (base gc) imm (struct (ser i31) (ser i31)))]
        load (path 1) copy ;; [(ref (base gc) imm (struct (ser i31) (ser i31)))] ->
                              [(ref (base gc) imm (struct (ser i31) (ser i31))) i31]
        local.set 1 ;; [i31] -> []
        drop ;; [(ref (base gc) imm (struct (ser i31) (ser i31)))] -> []
        local.get move 1 ;; [] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (prod i31 i31))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_split-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr)
        num_const 42 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 7 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        ungroup ;; [(prod i31 i31)] -> [i31 i31]
        local.set 2 ;; [i31] -> []
        local.set 1 ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 2 ;; [i31] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_let-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local (prod ptr ptr) ptr ptr)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        local.set 1 ;; [(prod i31 i31)] -> []
        local.get move 1 ;; [] -> [(prod i31 i31)]
        copy ;; [(prod i31 i31)] -> [(prod i31 i31) (prod i31 i31)]
        local.set 1 ;; [(prod i31 i31)] -> []
        ungroup ;; [(prod i31 i31)] -> [i31 i31]
        local.set 3 ;; [i31] -> []
        local.set 2 ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 2 ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 3 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 1 ;; [] -> [(prod i31 i31)]
        drop ;; [(prod i31 i31)] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_in_tuple-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (ref (base gc) imm (struct (ser (prod i31 i31)) (ser i31))))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        num_const 3 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [(prod i31 i31) i31] -> [(prod (prod i31 i31) i31)]
        new ;; [(prod (prod i31 i31) i31)] -> [(ref (base gc) imm (ser (prod (prod i31 i31) i31)))]
        cast ;; [(ref (base gc) imm (ser (prod (prod i31 i31) i31)))] ->
                [(ref (base gc) imm (struct (ser (prod i31 i31)) (ser i31)))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_of_tuple-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (prod (ref (base gc) imm (struct (ser i31) (ser i31))) i31))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        new ;; [(prod i31 i31)] -> [(ref (base gc) imm (ser (prod i31 i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31 i31)))] -> [(ref (base gc) imm (struct (ser i31) (ser i31)))]
        num_const 3 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [(ref (base gc) imm (struct (ser i31) (ser i31))) i31] ->
                 [(prod (ref (base gc) imm (struct (ser i31) (ser i31))) i31)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_ref-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (prod i31 i31)) (local (prod ptr ptr))
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        new ;; [(prod i31 i31)] -> [(ref (base gc) mut (ser (prod i31 i31)))]
        load (path) copy ;; [(ref (base gc) mut (ser (prod i31 i31)))] ->
                            [(ref (base gc) mut (ser (prod i31 i31))) (prod i31 i31)]
        local.set 1 ;; [(prod i31 i31)] -> []
        drop ;; [(ref (base gc) mut (ser (prod i31 i31)))] -> []
        local.get move 1 ;; [] -> [(prod i31 i31)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_fn-----------
    (module
      (func ((ref (base gc) imm (struct)) (prod i31 i31) -> i31) (local ptr ptr)
        local.get move 1 ;; [] -> [(prod i31 i31)]
        copy ;; [(prod i31 i31)] -> [(prod i31 i31) (prod i31 i31)]
        local.set 1 ;; [(prod i31 i31)] -> []
        ungroup ;; [(prod i31 i31)] -> [i31 i31]
        local.set 3 ;; [i31] -> []
        local.set 2 ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 2 ;; [i31] -> []
        local.get move 2 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 3 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(prod i31 i31)]
        drop ;; [(prod i31 i31)] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31))]
        group ;; [(ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31))] ->
                 [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))] ->
               [(ref (base gc) imm
                  (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (prod i31 i31) -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
          load (path 0) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
                                ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
          load (path 1) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
                                ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))
                                 (coderef ((var 0) (prod i31 i31) -> i31))]
          local.set 4 ;; [(coderef ((var 0) (prod i31 i31) -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) (prod i31 i31) -> i31))]
          local.set 5 ;; [(coderef ((var 0) (prod i31 i31) -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          num_const 6 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          group ;; [i31 i31] -> [(prod i31 i31)]
          local.get move 5 ;; [] -> [(coderef ((var 0) (prod i31 i31) -> i31))]
          copy ;; [(coderef ((var 0) (prod i31 i31) -> i31))] ->
                  [(coderef ((var 0) (prod i31 i31) -> i31)) (coderef ((var 0) (prod i31 i31) -> i31))]
          local.set 5 ;; [(coderef ((var 0) (prod i31 i31) -> i31))] -> []
          call_indirect ;; [(var 0) (prod i31 i31) (coderef ((var 0) (prod i31 i31) -> i31))] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) (prod i31 i31) -> i31))]
          drop ;; [(coderef ((var 0) (prod i31 i31) -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31)))))] -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (prod i31 i31) -> i31))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------utuple_ret-----------
    (module
      (func ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        num_const 9 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        group ;; [i31 i31] -> [(prod i31 i31)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31)))]
        group ;; [(ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31)))] ->
                 [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))]
        new ;; [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))] ->
               [(ref (base gc) imm
                  (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))))]
        cast ;; [(ref (base gc) imm
                   (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (prod i31 i31))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31)))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
          load (path 0) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
                                ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
          load (path 1) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
                                ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))
                                 (coderef ((var 0) i31 -> (prod i31 i31)))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (prod i31 i31)))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (prod i31 i31)))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (prod i31 i31)))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 4 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (prod i31 i31)))]
          copy ;; [(coderef ((var 0) i31 -> (prod i31 i31)))] ->
                  [(coderef ((var 0) i31 -> (prod i31 i31))) (coderef ((var 0) i31 -> (prod i31 i31)))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (prod i31 i31)))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (prod i31 i31)))] -> [(prod i31 i31)]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (prod i31 i31)))]
          drop ;; [(coderef ((var 0) i31 -> (prod i31 i31)))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31))))))] -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (prod i31 i31)))))))]
               -> [(prod i31 i31)]
        ungroup ;; [(prod i31 i31)] -> [i31 i31]
        local.set 7 ;; [i31] -> []
        local.set 6 ;; [i31] -> []
        local.get move 7 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 7 ;; [i31] -> []
        local.get move 6 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 7 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_make-----------
    (module
      (import ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))
      (func ((ref (base gc) imm (struct)) -> (ref (base mm) mut (ser i31))) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          copy ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                  [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))
                   (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                           [(ref (base mm) mut (ser i31))]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          drop ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
               -> [(ref (base mm) mut (ser i31))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_deref-----------
    (module
      (import ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))
      (func ((ref (base gc) imm (struct)) -> (prod (ref (base mm) mut (ser i31)) i31)) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          copy ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                  [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))
                   (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                           [(ref (base mm) mut (ser i31))]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          drop ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
               -> [(ref (base mm) mut (ser i31))]
        load (path) copy ;; [(ref (base mm) mut (ser i31))] -> [(ref (base mm) mut (ser i31)) i31]
        group ;; [(ref (base mm) mut (ser i31)) i31] -> [(prod (ref (base mm) mut (ser i31)) i31)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_assign-----------
    (module
      (import ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))
      (func ((ref (base gc) imm (struct)) -> (ref (base mm) mut (ser i31))) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          copy ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                  [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))
                   (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                           [(ref (base mm) mut (ser i31))]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          drop ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
               -> [(ref (base mm) mut (ser i31))]
        num_const 8 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        store (path) ;; [(ref (base mm) mut (ser i31)) i31] -> [(ref (base mm) mut (ser i31))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_let-----------
    (module
      (import ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))
      (func ((ref (base gc) imm (struct)) -> (ref (base mm) mut (ser i31))) (local ptr ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          copy ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                  [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))
                   (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                           [(ref (base mm) mut (ser i31))]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          drop ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
               -> [(ref (base mm) mut (ser i31))]
        local.set 6 ;; [(ref (base mm) mut (ser i31))] -> []
        local.get move 6 ;; [] -> [(ref (base mm) mut (ser i31))]
        num_const 9 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        store (path) ;; [(ref (base mm) mut (ser i31)) i31] -> [(ref (base mm) mut (ser i31))]
        local.get move 6 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_roundtrip-----------
    (module
      (import ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))
      (func ((ref (base gc) imm (struct)) -> (prod (ref (base mm) mut (ser i31)) i31)) (local ptr ptr ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) i31 -> (ref (base mm) mut (ser i31)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                   (ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))
                                 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 4 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          copy ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                  [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))
                   (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          local.set 5 ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] ->
                           [(ref (base mm) mut (ser i31))]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))]
          drop ;; [(coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> (ref (base mm) mut (ser i31))))))))]
               -> [(ref (base mm) mut (ser i31))]
        num_const 8 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        store (path) ;; [(ref (base mm) mut (ser i31)) i31] -> [(ref (base mm) mut (ser i31))]
        load (path) copy ;; [(ref (base mm) mut (ser i31))] -> [(ref (base mm) mut (ser i31)) i31]
        group ;; [(ref (base mm) mut (ser i31)) i31] -> [(prod (ref (base mm) mut (ser i31)) i31)]
        ungroup ;; [(prod (ref (base mm) mut (ser i31)) i31)] -> [(ref (base mm) mut (ser i31)) i31]
        local.set 7 ;; [i31] -> []
        local.set 6 ;; [(ref (base mm) mut (ser i31))] -> []
        local.get move 6 ;; [] -> [(ref (base mm) mut (ser i31))]
        local.get move 7 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 7 ;; [i31] -> []
        group ;; [(ref (base mm) mut (ser i31)) i31] -> [(prod (ref (base mm) mut (ser i31)) i31)]
        local.get move 6 ;; [] -> [(plug (prod i32))]
        drop ;; [(plug (prod i32))] -> []
        local.get move 7 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_reuse_rejected-----------
    FAILURE (InstrErr (error (NonRef Store (Plug (Prod ((Atom I32))))))
     (instr (Store (Path ())))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))
       (functions
        ((FunctionType () ((Ref (Base GC) Imm (Struct ())) I31)
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (table
        ((FunctionType () ((Ref (Base GC) Imm (Struct ())) I31)
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) Imm (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack (I31 (Plug (Prod ((Atom I32)))) (Ref (Base MM) Mut (Ser I31)))))))
    -----------sum_unit-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (ref (base gc) imm (variant (ser (ref (base gc) imm (struct))))))
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        inject_new 0 ;; [(ref (base gc) imm (struct))] ->
                        [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct)))))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------sum_option-----------
    (module
      (func ((ref (base gc) imm (struct)) -> (ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31))))
        num_const 15 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        inject_new 1 ;; [i31] -> [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_if-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 0 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 0 ;; [] -> [(num i32)]
        i32.eq ;; [(num i32) (num i32)] -> [(num i32)]
        if (localfx [0 => (ref (base gc) imm (struct))])
          num_const 1 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
        else
          num_const 2 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
        end ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------add-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------sub-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.sub ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------mul-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.mul ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------div-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.div_s ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------math-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31)
        num_const 2 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 6 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.mul ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        num_const 3 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.div_s ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_let-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr)
        num_const 10 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.set 1 ;; [i31] -> []
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------return_one-----------
    (module
      (func ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (func
          ((ref (base gc) imm (struct)) ->
          (exists.type (val ptr gcrefs) (val ptr gcrefs)
            (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))))
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------iife-----------
    (module
      (func ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser (coderef ((ref (base gc) imm (struct)) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                                 (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 4 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 5 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
          cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
          local.get move 5 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          copy ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] ->
                  [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))
                   (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 5 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          call_indirect ;; [(var 0) (ref (base gc) imm (struct)) (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
                           -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          drop ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -------------------------------
    (module
      (func ((ref (base gc) imm (struct)) i31 -> i31)
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> i31))]
        group ;; [(ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31))] ->
                 [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))] ->
               [(ref (base gc) imm
                  (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct))) (ser (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct))) (ser (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 1 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 0) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))) (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 1 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 1) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                                 (coderef ((var 0) i31 -> i31))]
          local.set 4 ;; [(coderef ((var 0) i31 -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 4 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          local.set 5 ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          copy ;; [(coderef ((var 0) i31 -> i31))] -> [(coderef ((var 0) i31 -> i31)) (coderef ((var 0) i31 -> i31))]
          local.set 5 ;; [(coderef ((var 0) i31 -> i31))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> i31))] -> [i31]
          local.get move 5 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          drop ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------add_one-----------
    (module
      (func ((ref (base gc) imm (struct)) i31 -> i31)
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        untag ;; [i31] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (table 0)
      (export "add1" (func 0)))
    -----------id-----------
    (module
      (func (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (table 0)
      (export "id" (func 0)))
    -----------assign-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr)
        num_const 0 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        new ;; [i31] -> [(ref (base gc) mut (ser i31))]
        local.set 1 ;; [(ref (base gc) mut (ser i31))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) mut (ser i31))]
        copy ;; [(ref (base gc) mut (ser i31))] -> [(ref (base gc) mut (ser i31)) (ref (base gc) mut (ser i31))]
        local.set 1 ;; [(ref (base gc) mut (ser i31))] -> []
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        store (path) ;; [(ref (base gc) mut (ser i31)) i31] -> [(ref (base gc) mut (ser i31))]
        local.set 2 ;; [(ref (base gc) mut (ser i31))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) mut (ser i31))]
        copy ;; [(ref (base gc) mut (ser i31))] -> [(ref (base gc) mut (ser i31)) (ref (base gc) mut (ser i31))]
        local.set 1 ;; [(ref (base gc) mut (ser i31))] -> []
        load (path) copy ;; [(ref (base gc) mut (ser i31))] -> [(ref (base gc) mut (ser i31)) i31]
        local.set 3 ;; [i31] -> []
        drop ;; [(ref (base gc) mut (ser i31))] -> []
        local.get move 3 ;; [] -> [i31]
        local.get move 2 ;; [] -> [(ref (base gc) mut (ser i31))]
        drop ;; [(ref (base gc) mut (ser i31))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) mut (ser i31))]
        drop ;; [(ref (base gc) mut (ser i31))] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------apply_id-----------
    (module
      (func (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] ->
                     [(coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 4 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 42 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] ->
                  [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type i31) ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                             -> [(coderef ((var 0) i31 -> i31))]
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> i31))] -> [i31]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm
                    (struct (ser (var 0))
                      (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "id" (func 0))
      (export "_start" (func 1)))
    -----------opt_case-----------
    (module
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr)
        num_const 42 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        inject_new 1 ;; [i31] -> [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
        local.set 1 ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
        copy ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] ->
                [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))
                 (ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
        local.set 1 ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] -> []
        case_load
          (localfx [0 => (ref (base gc) imm (struct))]
            [1 => (ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
            [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))])
          (0
            local.set 2 ;; [(ref (base gc) imm (struct))] -> []
            num_const 0 ;; [] -> [(num i32)]
            tag ;; [(num i32)] -> [i31]
            local.get move 2 ;; [] -> [(ref (base gc) imm (struct))]
            drop ;; [(ref (base gc) imm (struct))] -> [])
          (1
            local.set 3 ;; [i31] -> []
            local.get move 3 ;; [] -> [i31]
            copy ;; [i31] -> [i31 i31]
            local.set 3 ;; [i31] -> []
            local.get move 3 ;; [] -> [i31]
            drop ;; [i31] -> [])
        end ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] ->
               [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31))) i31]
        local.set 4 ;; [i31] -> []
        drop ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] -> []
        local.get move 4 ;; [] -> [i31]
        local.get move 1 ;; [] -> [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))]
        drop ;; [(ref (base gc) imm (variant (ser (ref (base gc) imm (struct))) (ser i31)))] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------poly_len-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (BaseM MemGC) Imm (ProdT []));
                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                  (RefT (BaseM MemGC) Imm
                    (VariantT
                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
              [ I31T]))
          (local ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get move 1 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
        copy ;; [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                ->
                [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))
                 (rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
        local.set 1 ;; [(rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                       -> []
        unfold ;; [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                  ->
                  [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser (var 0))
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
        case_load
          (localfx [0 => (ref (base gc) imm (struct))]
            [1 =>
            (rec (val ptr gcrefs)
              (ref (base gc) imm
                (variant (ser (ref (base gc) imm (struct))) (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
            [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
            [5 => (plug (prod i32))] [6 => (plug (prod i32))] [7 => (plug (prod i32))]
            [8 => (plug (prod i32))] [9 => (plug (prod i32))] [10 => (plug (prod i32))])
          (0
            local.set 2 ;; [(ref (base gc) imm (struct))] -> []
            num_const 0 ;; [] -> [(num i32)]
            tag ;; [(num i32)] -> [i31]
            local.get move 2 ;; [] -> [(ref (base gc) imm (struct))]
            drop ;; [(ref (base gc) imm (struct))] -> [])
          (1
            local.set 3 ;; [(ref (base gc) imm
                              (struct (ser (var 0))
                                (ser
                                  (rec (val ptr gcrefs)
                                    (ref (base gc) imm
                                      (variant (ser (ref (base gc) imm (struct)))
                                        (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
                           -> []
            num_const 1 ;; [] -> [(num i32)]
            tag ;; [(num i32)] -> [i31]
            untag ;; [i31] -> [(num i32)]
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
            cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
            coderef 0 ;; [] ->
                         [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (RefT (BaseM MemGC) Imm (ProdT []));
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                [ I31T])))]
            group ;; [(ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (BaseM MemGC) Imm (ProdT []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                            [ I31T])))]
                     ->
                     [(prod (ref (base gc) imm (struct))
                        (coderef
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (BaseM MemGC) Imm (ProdT []));
                                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (BaseM MemGC) Imm
                                    (VariantT
                                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                              [ I31T]))))]
            new ;; [(prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (BaseM MemGC) Imm (ProdT []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                            [ I31T]))))]
                   ->
                   [(ref (base gc) imm
                      (ser
                        (prod (ref (base gc) imm (struct))
                          (coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (RefT (BaseM MemGC) Imm (ProdT []));
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                [ I31T]))))))]
            cast ;; [(ref (base gc) imm
                       (ser
                         (prod (ref (base gc) imm (struct))
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (BaseM MemGC) Imm (ProdT []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                 [ I31T]))))))]
                    ->
                    [(ref (base gc) imm
                       (struct (ser (ref (base gc) imm (struct)))
                         (ser
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (BaseM MemGC) Imm (ProdT []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                 [ I31T]))))))]
            pack ;; [(ref (base gc) imm
                       (struct (ser (ref (base gc) imm (struct)))
                         (ser
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (BaseM MemGC) Imm (ProdT []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                 [ I31T]))))))]
                    ->
                    [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T])))))))]
            unpack (localfx [0 => (ref (base gc) imm (struct))]
                     [1 =>
                     (rec (val ptr gcrefs)
                       (ref (base gc) imm
                         (variant (ser (ref (base gc) imm (struct)))
                           (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                     [2 => (plug (prod i32))]
                     [3 =>
                     (ref (base gc) imm
                       (struct (ser (var 0))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
                     [4 => (plug (prod i32))] [5 => (plug (prod i32))] [6 => (plug (prod i32))]
                     [7 => (plug (prod i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32))]
                     [10 => (plug (prod i32))])
              local.set 4 ;; [(ref (base gc) imm
                                (struct (ser (var 0))
                                  (ser
                                    (coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                          [ I31T]))))))]
                             -> []
              local.get move 4 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 0))
                                       (ser
                                         (coderef
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                               [ I31T]))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
              local.set 4 ;; [(ref (base gc) imm
                                (struct (ser (var 0))
                                  (ser
                                    (coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                          [ I31T]))))))]
                             -> []
              load (path 0) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                                 [ I31T]))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                                 [ I31T]))))))
                                     (var 0)]
              local.set 5 ;; [(var 0)] -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
                      -> []
              local.get move 5 ;; [] -> [(var 0)]
              local.set 6 ;; [(var 0)] -> []
              local.get move 4 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 0))
                                       (ser
                                         (coderef
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                               [ I31T]))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
              local.set 4 ;; [(ref (base gc) imm
                                (struct (ser (var 0))
                                  (ser
                                    (coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                          [ I31T]))))))]
                             -> []
              load (path 1) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                                 [ I31T]))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                                 [ I31T]))))))
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                           [ I31T])))]
              local.set 7 ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                    [ I31T])))]
                             -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
                      -> []
              local.get move 7 ;; [] ->
                                  [(coderef
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                         [ I31T])))]
              local.set 8 ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                    [ I31T])))]
                             -> []
              local.get move 6 ;; [] -> [(var 0)]
              copy ;; [(var 0)] -> [(var 0) (var 0)]
              local.set 6 ;; [(var 0)] -> []
              local.get move 3 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 1))
                                       (ser
                                         (rec (val ptr gcrefs)
                                           (ref (base gc) imm
                                             (variant (ser (ref (base gc) imm (struct)))
                                               (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 1))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 1))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))
                       (ref (base gc) imm
                         (struct (ser (var 1))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
              local.set 3 ;; [(ref (base gc) imm
                                (struct (ser (var 1))
                                  (ser
                                    (rec (val ptr gcrefs)
                                      (ref (base gc) imm
                                        (variant (ser (ref (base gc) imm (struct)))
                                          (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                             -> []
              load (path 1) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 1))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 1))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
              local.set 9 ;; [(rec (val ptr gcrefs)
                                (ref (base gc) imm
                                  (variant (ser (ref (base gc) imm (struct)))
                                    (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                             -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 1))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                      -> []
              local.get move 9 ;; [] ->
                                  [(rec (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (variant (ser (ref (base gc) imm (struct)))
                                         (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
              local.get move 8 ;; [] ->
                                  [(coderef
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                         [ I31T])))]
              copy ;; [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T])))]
                      ->
                      [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T])))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T])))]
              local.set 8 ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                    [ I31T])))]
                             -> []
              inst (type (var 1)) ;; [(coderef
                                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 1);
                                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (VariantT
                                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                      (SerT
                                                        (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                            [ I31T])))]
                                     ->
                                     [(coderef
                                        ((var 0)
                                        (rec (val ptr gcrefs)
                                          (ref (base gc) imm
                                            (variant (ser (ref (base gc) imm (struct)))
                                              (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))
                                        -> i31))]
              call_indirect ;; [(var 0)
                                (rec (val ptr gcrefs)
                                  (ref (base gc) imm
                                    (variant (ser (ref (base gc) imm (struct)))
                                      (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))
                                (coderef
                                  ((var 0)
                                  (rec (val ptr gcrefs)
                                    (ref (base gc) imm
                                      (variant (ser (ref (base gc) imm (struct)))
                                        (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))
                                  -> i31))]
                               -> [i31]
              local.get move 8 ;; [] ->
                                  [(coderef
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                         [ I31T])))]
              drop ;; [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T])))]
                      -> []
              local.get move 6 ;; [] -> [(var 0)]
              drop ;; [(var 0)] -> []
              local.get move 4 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 0))
                                       (ser
                                         (coderef
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                               [ I31T]))))))]
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                   [ I31T]))))))]
                      -> []
            end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm
                        (struct (ser (var 0))
                          (ser
                            (coderef
                              (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (VarT 1);
                                    (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                  [ I31T])))))))]
                   -> [i31]
            untag ;; [i31] -> [(num i32)]
            i32.add ;; [(num i32) (num i32)] -> [(num i32)]
            tag ;; [(num i32)] -> [i31]
            local.get move 3 ;; [] ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
            drop ;; [(ref (base gc) imm
                       (struct (ser (var 0))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
                    -> [])
        end ;; [(ref (base gc) imm
                  (variant (ser (ref (base gc) imm (struct)))
                    (ser
                      (ref (base gc) imm
                        (struct (ser (var 0))
                          (ser
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
               ->
               [(ref (base gc) imm
                  (variant (ser (ref (base gc) imm (struct)))
                    (ser
                      (ref (base gc) imm
                        (struct (ser (var 0))
                          (ser
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))
                i31]
        local.set 10 ;; [i31] -> []
        drop ;; [(ref (base gc) imm
                   (variant (ser (ref (base gc) imm (struct)))
                     (ser
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
                -> []
        local.get move 10 ;; [] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
        drop ;; [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] ->
                     [(coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (BaseM MemGC) Imm (ProdT []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                            [ I31T])))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (BaseM MemGC) Imm (ProdT []));
                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (BaseM MemGC) Imm
                              (VariantT
                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                        [ I31T])))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (BaseM MemGC) Imm (ProdT []));
                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                              (RefT (BaseM MemGC) Imm
                                (VariantT
                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                    (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                          [ I31T]))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (BaseM MemGC) Imm (ProdT []));
                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (BaseM MemGC) Imm
                              (VariantT
                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                        [ I31T]))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (BaseM MemGC) Imm (ProdT []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                            [ I31T]))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (BaseM MemGC) Imm (ProdT []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T]))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (BaseM MemGC) Imm (ProdT []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T]))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (BaseM MemGC) Imm (ProdT []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                             [ I31T]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T])))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                      [ I31T]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                           [ I31T]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                      [ I31T]))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                             [ I31T]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                             [ I31T]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                           [ I31T]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                      [ I31T]))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                             [ I31T]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                             [ I31T]))))))
                                 (coderef
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 1);
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                       [ I31T])))]
          local.set 4 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                [ I31T])))]
                         -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                     [ I31T])))]
          local.set 5 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                [ I31T])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 1 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
          cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
          inject_new 0 ;; [(ref (base gc) imm (struct))] ->
                          [(ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser
                                 (ref (base gc) imm
                                   (struct (ser i31)
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
          fold ;; [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser i31)
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          group ;; [i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
                   ->
                   [(prod i31
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
          new ;; [(prod i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
                 ->
                 [(ref (base gc) imm
                    (ser
                      (prod i31
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          cast ;; [(ref (base gc) imm
                     (ser
                       (prod i31
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser i31)
                       (ser
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          inject_new 1 ;; [(ref (base gc) imm
                             (struct (ser i31)
                               (ser
                                 (rec (val ptr gcrefs)
                                   (ref (base gc) imm
                                     (variant (ser (ref (base gc) imm (struct)))
                                       (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                          ->
                          [(ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser
                                 (ref (base gc) imm
                                   (struct (ser i31)
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
          fold ;; [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser i31)
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                     [ I31T])))]
          copy ;; [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                         [ I31T])))]
                  ->
                  [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                         [ I31T])))
                   (coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                         [ I31T])))]
          local.set 5 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                [ I31T])))]
                         -> []
          inst (type i31) ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                    [ I31T])))]
                             ->
                             [(coderef
                                ((var 0)
                                (rec (val ptr gcrefs)
                                  (ref (base gc) imm
                                    (variant (ser (ref (base gc) imm (struct)))
                                      (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))
                                -> i31))]
          call_indirect ;; [(var 0)
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))
                            (coderef
                              ((var 0)
                              (rec (val ptr gcrefs)
                                (ref (base gc) imm
                                  (variant (ser (ref (base gc) imm (struct)))
                                    (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))
                              -> i31))]
                           -> [i31]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                     [ I31T])))]
          drop ;; [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                         [ I31T])))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                                           [ I31T]))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                               [ I31T]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm
                    (struct (ser (var 0))
                      (ser
                        (coderef
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (VarT 1);
                                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (BaseM MemGC) Imm
                                    (VariantT
                                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]
                              [ I31T])))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "len" (func 0))
      (export "_start" (func 1)))
    -----------poly_map-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
              (MonoFunT
                [ (RefT (BaseM MemGC) Imm (ProdT []));
                  (RefT (BaseM MemGC) Imm
                    (ProdT
                      [ (SerT
                        (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs) (VALTYPE (AtomR PtrR) GCRefs)
                          (RefT (BaseM MemGC) Imm
                            (ProdT
                              [ (SerT (VarT 0)); (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                        (SerT
                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (BaseM MemGC) Imm
                              (VariantT
                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                  (RefT (BaseM MemGC) Imm
                    (VariantT
                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))
          (local ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get move 1 ;; [] ->
                            [(ref (base gc) imm
                               (struct
                                 (ser
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                 (ser
                                   (rec (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (variant (ser (ref (base gc) imm (struct)))
                                         (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
        copy ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                     (ser
                       (rec (val ptr gcrefs)
                         (ref (base gc) imm
                           (variant (ser (ref (base gc) imm (struct)))
                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                ->
                [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                     (ser
                       (rec (val ptr gcrefs)
                         (ref (base gc) imm
                           (variant (ser (ref (base gc) imm (struct)))
                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))
                 (ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                     (ser
                       (rec (val ptr gcrefs)
                         (ref (base gc) imm
                           (variant (ser (ref (base gc) imm (struct)))
                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
        local.set 1 ;; [(ref (base gc) imm
                          (struct
                            (ser
                              (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                            (ser
                              (rec (val ptr gcrefs)
                                (ref (base gc) imm
                                  (variant (ser (ref (base gc) imm (struct)))
                                    (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                       -> []
        load (path 0) copy ;; [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                   (ser
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                              ->
                              [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                   (ser
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                       -> []
        load (path 1) copy ;; [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                   (ser
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                              ->
                              [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                   (ser
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
        local.set 3 ;; [(rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                       -> []
        drop ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                     (ser
                       (rec (val ptr gcrefs)
                         (ref (base gc) imm
                           (variant (ser (ref (base gc) imm (struct)))
                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                -> []
        local.get move 3 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
        copy ;; [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                ->
                [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))
                 (rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
        local.set 3 ;; [(rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                       -> []
        unfold ;; [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                  ->
                  [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser (var 1))
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))))))]
        case_load
          (localfx [0 => (ref (base gc) imm (struct))]
            [1 =>
            (ref (base gc) imm
              (struct
                (ser
                  (exists.type (val ptr gcrefs) (val ptr gcrefs)
                    (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                (ser
                  (rec (val ptr gcrefs)
                    (ref (base gc) imm
                      (variant (ser (ref (base gc) imm (struct)))
                        (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
            [2 =>
            (exists.type (val ptr gcrefs) (val ptr gcrefs)
              (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
            [3 =>
            (rec (val ptr gcrefs)
              (ref (base gc) imm
                (variant (ser (ref (base gc) imm (struct))) (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
            [4 => (plug (prod i32))] [5 => (plug (prod i32))] [6 => (plug (prod i32))]
            [7 => (plug (prod i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32))]
            [10 => (plug (prod i32))] [11 => (plug (prod i32))] [12 => (plug (prod i32))]
            [13 => (plug (prod i32))] [14 => (plug (prod i32))] [15 => (plug (prod i32))]
            [16 => (plug (prod i32))] [17 => (plug (prod i32))] [18 => (plug (prod i32))])
          (0
            local.set 4 ;; [(ref (base gc) imm (struct))] -> []
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
            cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
            inject_new 0 ;; [(ref (base gc) imm (struct))] ->
                            [(ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser
                                   (ref (base gc) imm
                                     (struct (ser (var 0))
                                       (ser
                                         (rec (val ptr gcrefs)
                                           (ref (base gc) imm
                                             (variant (ser (ref (base gc) imm (struct)))
                                               (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
            fold ;; [(ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser
                           (ref (base gc) imm
                             (struct (ser (var 0))
                               (ser
                                 (rec (val ptr gcrefs)
                                   (ref (base gc) imm
                                     (variant (ser (ref (base gc) imm (struct)))
                                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
                    ->
                    [(rec (val ptr gcrefs)
                       (ref (base gc) imm
                         (variant (ser (ref (base gc) imm (struct)))
                           (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
            local.get move 4 ;; [] -> [(ref (base gc) imm (struct))]
            drop ;; [(ref (base gc) imm (struct))] -> [])
          (1
            local.set 5 ;; [(ref (base gc) imm
                              (struct (ser (var 1))
                                (ser
                                  (rec (val ptr gcrefs)
                                    (ref (base gc) imm
                                      (variant (ser (ref (base gc) imm (struct)))
                                        (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                           -> []
            local.get move 2 ;; [] ->
                                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
            copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                    ->
                    [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))
                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
            local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                              (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                           -> []
            unpack (localfx [0 => (ref (base gc) imm (struct))]
                     [1 =>
                     (ref (base gc) imm
                       (struct
                         (ser
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                     [2 =>
                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                     [3 =>
                     (rec (val ptr gcrefs)
                       (ref (base gc) imm
                         (variant (ser (ref (base gc) imm (struct)))
                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                     [4 => (plug (prod i32))]
                     [5 =>
                     (ref (base gc) imm
                       (struct (ser (var 1))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                     [6 => (plug (prod i32))] [7 => (plug (prod i32))] [8 => (plug (prod i32))]
                     [9 => (plug (prod i32))] [10 => (plug (prod i32))] [11 => (plug (prod i32))]
                     [12 => (plug (prod i32))] [13 => (plug (prod i32))]
                     [14 => (plug (prod i32))] [15 => (plug (prod i32))]
                     [16 => (plug (prod i32))] [17 => (plug (prod i32))]
                     [18 => (plug (prod i32))])
              local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] ->
                             []
              local.get move 6 ;; [] ->
                                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
              copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] ->
                      [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
              local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] ->
                             []
              load (path 0) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))
                                     (var 0)]
              local.set 7 ;; [(var 0)] -> []
              drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] -> []
              local.get move 7 ;; [] -> [(var 0)]
              local.set 8 ;; [(var 0)] -> []
              local.get move 6 ;; [] ->
                                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
              copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] ->
                      [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
              local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] ->
                             []
              load (path 1) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))
                                     (coderef ((var 0) (var 2) -> (var 1)))]
              local.set 9 ;; [(coderef ((var 0) (var 2) -> (var 1)))] -> []
              drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] -> []
              local.get move 9 ;; [] -> [(coderef ((var 0) (var 2) -> (var 1)))]
              local.set 10 ;; [(coderef ((var 0) (var 2) -> (var 1)))] -> []
              local.get move 8 ;; [] -> [(var 0)]
              copy ;; [(var 0)] -> [(var 0) (var 0)]
              local.set 8 ;; [(var 0)] -> []
              local.get move 5 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 2))
                                       (ser
                                         (rec (val ptr gcrefs)
                                           (ref (base gc) imm
                                             (variant (ser (ref (base gc) imm (struct)))
                                               (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                       (ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              local.set 5 ;; [(ref (base gc) imm
                                (struct (ser (var 2))
                                  (ser
                                    (rec (val ptr gcrefs)
                                      (ref (base gc) imm
                                        (variant (ser (ref (base gc) imm (struct)))
                                          (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                             -> []
              load (path 0) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 2))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 2))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                                     (var 2)]
              local.set 11 ;; [(var 2)] -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                      -> []
              local.get move 11 ;; [] -> [(var 2)]
              local.get move 10 ;; [] -> [(coderef ((var 0) (var 2) -> (var 1)))]
              copy ;; [(coderef ((var 0) (var 2) -> (var 1)))] ->
                      [(coderef ((var 0) (var 2) -> (var 1))) (coderef ((var 0) (var 2) -> (var 1)))]
              local.set 10 ;; [(coderef ((var 0) (var 2) -> (var 1)))] -> []
              call_indirect ;; [(var 0) (var 2) (coderef ((var 0) (var 2) -> (var 1)))] -> [(var 1)]
              local.get move 10 ;; [] -> [(coderef ((var 0) (var 2) -> (var 1)))]
              drop ;; [(coderef ((var 0) (var 2) -> (var 1)))] -> []
              local.get move 8 ;; [] -> [(var 0)]
              drop ;; [(var 0)] -> []
              local.get move 6 ;; [] ->
                                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))]
              drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))] -> []
            end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                   -> [(var 0)]
            group ;; [] -> [(prod)]
            new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
            cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
            coderef 0 ;; [] ->
                         [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (RefT (BaseM MemGC) Imm (ProdT []));
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT
                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (ProdT
                                                [ (SerT (VarT 0));
                                                  (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                          (SerT
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
            group ;; [(ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (BaseM MemGC) Imm (ProdT []));
                                (RefT (BaseM MemGC) Imm
                                  (ProdT
                                    [ (SerT
                                      (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                        (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (ProdT
                                            [ (SerT (VarT 0));
                                              (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                      (SerT
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                              [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                     ->
                     [(prod (ref (base gc) imm (struct))
                        (coderef
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (RefT (BaseM MemGC) Imm (ProdT []));
                                  (RefT (BaseM MemGC) Imm
                                    (ProdT
                                      [ (SerT
                                        (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                          (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (ProdT
                                              [ (SerT (VarT 0));
                                                (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                        (SerT
                                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (VariantT
                                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (BaseM MemGC) Imm
                                    (VariantT
                                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))]
            new ;; [(prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (BaseM MemGC) Imm (ProdT []));
                                (RefT (BaseM MemGC) Imm
                                  (ProdT
                                    [ (SerT
                                      (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                        (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (ProdT
                                            [ (SerT (VarT 0));
                                              (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                      (SerT
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                              [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))]
                   ->
                   [(ref (base gc) imm
                      (ser
                        (prod (ref (base gc) imm (struct))
                          (coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (RefT (BaseM MemGC) Imm (ProdT []));
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT
                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (ProdT
                                                [ (SerT (VarT 0));
                                                  (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                          (SerT
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
            cast ;; [(ref (base gc) imm
                       (ser
                         (prod (ref (base gc) imm (struct))
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (RefT (BaseM MemGC) Imm (ProdT []));
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT
                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (ProdT
                                                 [ (SerT (VarT 0));
                                                   (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                           (SerT
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                    ->
                    [(ref (base gc) imm
                       (struct (ser (ref (base gc) imm (struct)))
                         (ser
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (RefT (BaseM MemGC) Imm (ProdT []));
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT
                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (ProdT
                                                 [ (SerT (VarT 0));
                                                   (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                           (SerT
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
            pack ;; [(ref (base gc) imm
                       (struct (ser (ref (base gc) imm (struct)))
                         (ser
                           (coderef
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (RefT (BaseM MemGC) Imm (ProdT []));
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT
                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (ProdT
                                                 [ (SerT (VarT 0));
                                                   (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                           (SerT
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (VariantT
                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                           (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                    ->
                    [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))))))]
            unpack (localfx [0 => (ref (base gc) imm (struct))]
                     [1 =>
                     (ref (base gc) imm
                       (struct
                         (ser
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                     [2 =>
                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                     [3 =>
                     (rec (val ptr gcrefs)
                       (ref (base gc) imm
                         (variant (ser (ref (base gc) imm (struct)))
                           (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                     [4 => (plug (prod i32))]
                     [5 =>
                     (ref (base gc) imm
                       (struct (ser (var 1))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                     [6 => (plug (prod i32))] [7 => (plug (prod i32))] [8 => (plug (prod i32))]
                     [9 => (plug (prod i32))] [10 => (plug (prod i32))] [11 => (plug (prod i32))]
                     [12 => (plug (prod i32))] [13 => (plug (prod i32))]
                     [14 => (plug (prod i32))] [15 => (plug (prod i32))]
                     [16 => (plug (prod i32))] [17 => (plug (prod i32))]
                     [18 => (plug (prod i32))])
              local.set 12 ;; [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                              -> []
              local.get move 12 ;; [] ->
                                   [(ref (base gc) imm
                                      (struct (ser (var 0))
                                        (ser
                                          (coderef
                                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                (MonoFunT
                                                  [ (VarT 2);
                                                    (RefT (BaseM MemGC) Imm
                                                      (ProdT
                                                        [ (SerT
                                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                            (VALTYPE (AtomR PtrR) GCRefs)
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT
                                                                [ (SerT (VarT 0));
                                                                  (SerT
                                                                    (CodeRefT
                                                                      (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                          (SerT
                                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                              (RefT (BaseM MemGC) Imm
                                                                (VariantT
                                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                    (SerT
                                                                      (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
              local.set 12 ;; [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                              -> []
              load (path 0) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (MonoFunT
                                                   [ (VarT 2);
                                                     (RefT (BaseM MemGC) Imm
                                                       (ProdT
                                                         [ (SerT
                                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (VALTYPE (AtomR PtrR) GCRefs)
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT
                                                                 [ (SerT (VarT 0));
                                                                   (SerT
                                                                     (CodeRefT
                                                                       (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                           (SerT
                                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (RefT (BaseM MemGC) Imm
                                                                 (VariantT
                                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                     (SerT
                                                                       (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (MonoFunT
                                                   [ (VarT 2);
                                                     (RefT (BaseM MemGC) Imm
                                                       (ProdT
                                                         [ (SerT
                                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (VALTYPE (AtomR PtrR) GCRefs)
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT
                                                                 [ (SerT (VarT 0));
                                                                   (SerT
                                                                     (CodeRefT
                                                                       (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                           (SerT
                                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (RefT (BaseM MemGC) Imm
                                                                 (VariantT
                                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                     (SerT
                                                                       (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                                     (var 0)]
              local.set 13 ;; [(var 0)] -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                      -> []
              local.get move 13 ;; [] -> [(var 0)]
              local.set 14 ;; [(var 0)] -> []
              local.get move 12 ;; [] ->
                                   [(ref (base gc) imm
                                      (struct (ser (var 0))
                                        (ser
                                          (coderef
                                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                (MonoFunT
                                                  [ (VarT 2);
                                                    (RefT (BaseM MemGC) Imm
                                                      (ProdT
                                                        [ (SerT
                                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                            (VALTYPE (AtomR PtrR) GCRefs)
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT
                                                                [ (SerT (VarT 0));
                                                                  (SerT
                                                                    (CodeRefT
                                                                      (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                          (SerT
                                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                              (RefT (BaseM MemGC) Imm
                                                                (VariantT
                                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                    (SerT
                                                                      (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                       (ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
              local.set 12 ;; [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                              -> []
              load (path 1) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (MonoFunT
                                                   [ (VarT 2);
                                                     (RefT (BaseM MemGC) Imm
                                                       (ProdT
                                                         [ (SerT
                                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (VALTYPE (AtomR PtrR) GCRefs)
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT
                                                                 [ (SerT (VarT 0));
                                                                   (SerT
                                                                     (CodeRefT
                                                                       (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                           (SerT
                                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (RefT (BaseM MemGC) Imm
                                                                 (VariantT
                                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                     (SerT
                                                                       (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 0))
                                         (ser
                                           (coderef
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (MonoFunT
                                                   [ (VarT 2);
                                                     (RefT (BaseM MemGC) Imm
                                                       (ProdT
                                                         [ (SerT
                                                           (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (VALTYPE (AtomR PtrR) GCRefs)
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT
                                                                 [ (SerT (VarT 0));
                                                                   (SerT
                                                                     (CodeRefT
                                                                       (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                           (SerT
                                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (RefT (BaseM MemGC) Imm
                                                                 (VariantT
                                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                     (SerT
                                                                       (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                   [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
              local.set 15 ;; [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                              -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                      -> []
              local.get move 15 ;; [] ->
                                   [(coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 2);
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT
                                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (VALTYPE (AtomR PtrR) GCRefs)
                                                      (RefT (BaseM MemGC) Imm
                                                        (ProdT
                                                          [ (SerT (VarT 0));
                                                            (SerT
                                                              (CodeRefT
                                                                (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                    (SerT
                                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (VariantT
                                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                              (SerT
                                                                (RefT (BaseM MemGC) Imm
                                                                  (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
              local.set 16 ;; [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                              -> []
              local.get move 14 ;; [] -> [(var 0)]
              copy ;; [(var 0)] -> [(var 0) (var 0)]
              local.set 14 ;; [(var 0)] -> []
              local.get move 2 ;; [] ->
                                  [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))]
              copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))]
                      ->
                      [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))]
              local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))]
                             -> []
              local.get move 5 ;; [] ->
                                  [(ref (base gc) imm
                                     (struct (ser (var 2))
                                       (ser
                                         (rec (val ptr gcrefs)
                                           (ref (base gc) imm
                                             (variant (ser (ref (base gc) imm (struct)))
                                               (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              copy ;; [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                      ->
                      [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                       (ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              local.set 5 ;; [(ref (base gc) imm
                                (struct (ser (var 2))
                                  (ser
                                    (rec (val ptr gcrefs)
                                      (ref (base gc) imm
                                        (variant (ser (ref (base gc) imm (struct)))
                                          (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                             -> []
              load (path 1) copy ;; [(ref (base gc) imm
                                       (struct (ser (var 2))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                                    ->
                                    [(ref (base gc) imm
                                       (struct (ser (var 2))
                                         (ser
                                           (rec (val ptr gcrefs)
                                             (ref (base gc) imm
                                               (variant (ser (ref (base gc) imm (struct)))
                                                 (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                                     (rec (val ptr gcrefs)
                                       (ref (base gc) imm
                                         (variant (ser (ref (base gc) imm (struct)))
                                           (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0))))))))]
              local.set 17 ;; [(rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0))))))))]
                              -> []
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 2))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                      -> []
              local.get move 17 ;; [] ->
                                   [(rec (val ptr gcrefs)
                                      (ref (base gc) imm
                                        (variant (ser (ref (base gc) imm (struct)))
                                          (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0))))))))]
              group ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0))))))))]
                       ->
                       [(prod
                          (exists.type (val ptr gcrefs) (val ptr gcrefs)
                            (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                          (rec (val ptr gcrefs)
                            (ref (base gc) imm
                              (variant (ser (ref (base gc) imm (struct)))
                                (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))]
              new ;; [(prod
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))]
                     ->
                     [(ref (base gc) imm
                        (ser
                          (prod
                            (exists.type (val ptr gcrefs) (val ptr gcrefs)
                              (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              cast ;; [(ref (base gc) imm
                         (ser
                           (prod
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2)))))))
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
                      ->
                      [(ref (base gc) imm
                         (struct
                           (ser
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2))))))))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))]
              local.get move 16 ;; [] ->
                                   [(coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 2);
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT
                                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (VALTYPE (AtomR PtrR) GCRefs)
                                                      (RefT (BaseM MemGC) Imm
                                                        (ProdT
                                                          [ (SerT (VarT 0));
                                                            (SerT
                                                              (CodeRefT
                                                                (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                    (SerT
                                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (VariantT
                                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                              (SerT
                                                                (RefT (BaseM MemGC) Imm
                                                                  (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
              copy ;; [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 2);
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                      ->
                      [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 2);
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 2);
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
              local.set 16 ;; [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                              -> []
              inst (type (var 2)) ;; [(coderef
                                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                          (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (MonoFunT
                                              [ (VarT 2);
                                                (RefT (BaseM MemGC) Imm
                                                  (ProdT
                                                    [ (SerT
                                                      (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (ProdT
                                                            [ (SerT (VarT 0));
                                                              (SerT
                                                                (CodeRefT
                                                                  (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                      (SerT
                                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                          (RefT (BaseM MemGC) Imm
                                                            (VariantT
                                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                (SerT
                                                                  (RefT (BaseM MemGC) Imm
                                                                    (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                              [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (VariantT
                                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                      (SerT
                                                        (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                                     ->
                                     [(coderef
                                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 1);
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT
                                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (VALTYPE (AtomR PtrR) GCRefs)
                                                      (RefT (BaseM MemGC) Imm
                                                        (ProdT
                                                          [ (SerT (VarT 0));
                                                            (SerT
                                                              (CodeRefT
                                                                (InnerFunT (MonoFunT [ (VarT 0); (VarT 4)] [ (VarT 1)]))))]))));
                                                    (SerT
                                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (VariantT
                                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                              (SerT
                                                                (RefT (BaseM MemGC) Imm
                                                                  (ProdT [ (SerT (VarT 4)); (SerT (VarT 0))])))]))))]))]
                                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))]
              inst (type (var 1)) ;; [(coderef
                                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 1);
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT
                                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (VALTYPE (AtomR PtrR) GCRefs)
                                                      (RefT (BaseM MemGC) Imm
                                                        (ProdT
                                                          [ (SerT (VarT 0));
                                                            (SerT
                                                              (CodeRefT
                                                                (InnerFunT (MonoFunT [ (VarT 0); (VarT 4)] [ (VarT 1)]))))]))));
                                                    (SerT
                                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (VariantT
                                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                              (SerT
                                                                (RefT (BaseM MemGC) Imm
                                                                  (ProdT [ (SerT (VarT 4)); (SerT (VarT 0))])))]))))]))]
                                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))]
                                     ->
                                     [(coderef
                                        ((var 0)
                                        (ref (base gc) imm
                                          (struct
                                            (ser
                                              (exists.type (val ptr gcrefs)
                                                (val ptr gcrefs)
                                                (ref (base gc) imm
                                                  (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2))))))))
                                            (ser
                                              (rec (val ptr gcrefs)
                                                (ref (base gc) imm
                                                  (variant (ser (ref (base gc) imm (struct)))
                                                    (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                                        ->
                                        (rec (val ptr gcrefs)
                                          (ref (base gc) imm
                                            (variant (ser (ref (base gc) imm (struct)))
                                              (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))]
              call_indirect ;; [(var 0)
                                (ref (base gc) imm
                                  (struct
                                    (ser
                                      (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                        (ref (base gc) imm
                                          (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2))))))))
                                    (ser
                                      (rec (val ptr gcrefs)
                                        (ref (base gc) imm
                                          (variant (ser (ref (base gc) imm (struct)))
                                            (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                                (coderef
                                  ((var 0)
                                  (ref (base gc) imm
                                    (struct
                                      (ser
                                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                          (ref (base gc) imm
                                            (struct (ser (var 0)) (ser (coderef ((var 0) (var 3) -> (var 2))))))))
                                      (ser
                                        (rec (val ptr gcrefs)
                                          (ref (base gc) imm
                                            (variant (ser (ref (base gc) imm (struct)))
                                              (ser (ref (base gc) imm (struct (ser (var 3)) (ser (var 0)))))))))))
                                  ->
                                  (rec (val ptr gcrefs)
                                    (ref (base gc) imm
                                      (variant (ser (ref (base gc) imm (struct)))
                                        (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))]
                               ->
                               [(rec (val ptr gcrefs)
                                  (ref (base gc) imm
                                    (variant (ser (ref (base gc) imm (struct)))
                                      (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
              local.get move 16 ;; [] ->
                                   [(coderef
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 2);
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT
                                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (VALTYPE (AtomR PtrR) GCRefs)
                                                      (RefT (BaseM MemGC) Imm
                                                        (ProdT
                                                          [ (SerT (VarT 0));
                                                            (SerT
                                                              (CodeRefT
                                                                (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                    (SerT
                                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (RefT (BaseM MemGC) Imm
                                                          (VariantT
                                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                              (SerT
                                                                (RefT (BaseM MemGC) Imm
                                                                  (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
              drop ;; [(coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 2);
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                      -> []
              local.get move 14 ;; [] -> [(var 0)]
              drop ;; [(var 0)] -> []
              local.get move 12 ;; [] ->
                                   [(ref (base gc) imm
                                      (struct (ser (var 0))
                                        (ser
                                          (coderef
                                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                (MonoFunT
                                                  [ (VarT 2);
                                                    (RefT (BaseM MemGC) Imm
                                                      (ProdT
                                                        [ (SerT
                                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                            (VALTYPE (AtomR PtrR) GCRefs)
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT
                                                                [ (SerT (VarT 0));
                                                                  (SerT
                                                                    (CodeRefT
                                                                      (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                          (SerT
                                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                              (RefT (BaseM MemGC) Imm
                                                                (VariantT
                                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                    (SerT
                                                                      (RefT
                                                                        (BaseM MemGC) Imm
                                                                        (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
              drop ;; [(ref (base gc) imm
                         (struct (ser (var 0))
                           (ser
                             (coderef
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 2);
                                       (RefT (BaseM MemGC) Imm
                                         (ProdT
                                           [ (SerT
                                             (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                               (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT (VarT 0));
                                                     (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                             (SerT
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                     [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                      -> []
            end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm
                        (struct (ser (var 0))
                          (ser
                            (coderef
                              (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 2);
                                      (RefT (BaseM MemGC) Imm
                                        (ProdT
                                          [ (SerT
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                              (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT (VarT 0));
                                                    (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                            (SerT
                                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (VariantT
                                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                      (SerT
                                                        (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                    [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))))))]
                   ->
                   [(rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
            group ;; [(var 0)
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                     ->
                     [(prod (var 0)
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))]
            new ;; [(prod (var 0)
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))]
                   ->
                   [(ref (base gc) imm
                      (ser
                        (prod (var 0)
                          (rec (val ptr gcrefs)
                            (ref (base gc) imm
                              (variant (ser (ref (base gc) imm (struct)))
                                (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
            cast ;; [(ref (base gc) imm
                       (ser
                         (prod (var 0)
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
                    ->
                    [(ref (base gc) imm
                       (struct (ser (var 0))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
            inject_new 1 ;; [(ref (base gc) imm
                               (struct (ser (var 0))
                                 (ser
                                   (rec (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (variant (ser (ref (base gc) imm (struct)))
                                         (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0)))))))))))]
                            ->
                            [(ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser
                                   (ref (base gc) imm
                                     (struct (ser (var 0))
                                       (ser
                                         (rec (val ptr gcrefs)
                                           (ref (base gc) imm
                                             (variant (ser (ref (base gc) imm (struct)))
                                               (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
            fold ;; [(ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser
                           (ref (base gc) imm
                             (struct (ser (var 0))
                               (ser
                                 (rec (val ptr gcrefs)
                                   (ref (base gc) imm
                                     (variant (ser (ref (base gc) imm (struct)))
                                       (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))))))))]
                    ->
                    [(rec (val ptr gcrefs)
                       (ref (base gc) imm
                         (variant (ser (ref (base gc) imm (struct)))
                           (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
            local.get move 5 ;; [] ->
                                [(ref (base gc) imm
                                   (struct (ser (var 1))
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
            drop ;; [(ref (base gc) imm
                       (struct (ser (var 1))
                         (ser
                           (rec (val ptr gcrefs)
                             (ref (base gc) imm
                               (variant (ser (ref (base gc) imm (struct)))
                                 (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                    -> [])
        end ;; [(ref (base gc) imm
                  (variant (ser (ref (base gc) imm (struct)))
                    (ser
                      (ref (base gc) imm
                        (struct (ser (var 1))
                          (ser
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))))))]
               ->
               [(ref (base gc) imm
                  (variant (ser (ref (base gc) imm (struct)))
                    (ser
                      (ref (base gc) imm
                        (struct (ser (var 1))
                          (ser
                            (rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))))))
                (rec (val ptr gcrefs)
                  (ref (base gc) imm
                    (variant (ser (ref (base gc) imm (struct)))
                      (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
        local.set 18 ;; [(rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
                        -> []
        drop ;; [(ref (base gc) imm
                   (variant (ser (ref (base gc) imm (struct)))
                     (ser
                       (ref (base gc) imm
                         (struct (ser (var 1))
                           (ser
                             (rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))))))))]
                -> []
        local.get move 18 ;; [] ->
                             [(rec (val ptr gcrefs)
                                (ref (base gc) imm
                                  (variant (ser (ref (base gc) imm (struct)))
                                    (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))))]
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1)))))))]
                -> []
        local.get move 3 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (base gc) imm
                                 (variant (ser (ref (base gc) imm (struct)))
                                   (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
        drop ;; [(rec (val ptr gcrefs)
                   (ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0))))))))]
                -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] ->
                            [(ref (base gc) imm
                               (struct
                                 (ser
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                                 (ser
                                   (rec (val ptr gcrefs)
                                     (ref (base gc) imm
                                       (variant (ser (ref (base gc) imm (struct)))
                                         (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
        drop ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (var 2) -> (var 1))))))))
                     (ser
                       (rec (val ptr gcrefs)
                         (ref (base gc) imm
                           (variant (ser (ref (base gc) imm (struct)))
                             (ser (ref (base gc) imm (struct (ser (var 2)) (ser (var 0)))))))))))]
                -> [])
      (func ((ref (base gc) imm (struct)) i31 -> i31)
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        untag ;; [i31] -> [(num i32)]
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        untag ;; [i31] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (func
          ((ref (base gc) imm (struct)) ->
          (rec (val ptr gcrefs)
            (ref (base gc) imm
              (variant (ser (ref (base gc) imm (struct))) (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))
          (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] ->
                     [(coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (BaseM MemGC) Imm (ProdT []));
                                (RefT (BaseM MemGC) Imm
                                  (ProdT
                                    [ (SerT
                                      (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                        (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (ProdT
                                            [ (SerT (VarT 0));
                                              (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                      (SerT
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                              [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (BaseM MemGC) Imm (ProdT []));
                            (RefT (BaseM MemGC) Imm
                              (ProdT
                                [ (SerT
                                  (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                    (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT (VarT 0));
                                          (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                  (SerT
                                    (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                          [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (BaseM MemGC) Imm
                              (VariantT
                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (BaseM MemGC) Imm (ProdT []));
                              (RefT (BaseM MemGC) Imm
                                (ProdT
                                  [ (SerT
                                    (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                      (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (ProdT
                                          [ (SerT (VarT 0));
                                            (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                    (SerT
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                            [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                              (RefT (BaseM MemGC) Imm
                                (VariantT
                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                    (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (BaseM MemGC) Imm (ProdT []));
                            (RefT (BaseM MemGC) Imm
                              (ProdT
                                [ (SerT
                                  (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                    (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT (VarT 0));
                                          (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                  (SerT
                                    (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                          [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (BaseM MemGC) Imm
                              (VariantT
                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (BaseM MemGC) Imm (ProdT []));
                                (RefT (BaseM MemGC) Imm
                                  (ProdT
                                    [ (SerT
                                      (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                        (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (ProdT
                                            [ (SerT (VarT 0));
                                              (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                      (SerT
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                              [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (BaseM MemGC) Imm
                                  (VariantT
                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (RefT (BaseM MemGC) Imm (ProdT []));
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (RefT (BaseM MemGC) Imm (ProdT []));
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (RefT (BaseM MemGC) Imm (ProdT []));
                                 (RefT (BaseM MemGC) Imm
                                   (ProdT
                                     [ (SerT
                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                         (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT (VarT 0));
                                               (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                       (SerT
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (BaseM MemGC) Imm
                                   (VariantT
                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                       (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                      (MonoFunT
                                        [ (VarT 2);
                                          (RefT (BaseM MemGC) Imm
                                            (ProdT
                                              [ (SerT
                                                (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (VALTYPE (AtomR PtrR) GCRefs)
                                                  (RefT (BaseM MemGC) Imm
                                                    (ProdT
                                                      [ (SerT (VarT 0));
                                                        (SerT
                                                          (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                (SerT
                                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                        [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                      (MonoFunT
                                        [ (VarT 2);
                                          (RefT (BaseM MemGC) Imm
                                            (ProdT
                                              [ (SerT
                                                (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (VALTYPE (AtomR PtrR) GCRefs)
                                                  (RefT (BaseM MemGC) Imm
                                                    (ProdT
                                                      [ (SerT (VarT 0));
                                                        (SerT
                                                          (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                (SerT
                                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                        [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 2);
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT
                                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (ProdT
                                                             [ (SerT (VarT 0));
                                                               (SerT
                                                                 (CodeRefT
                                                                   (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                       (SerT
                                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (RefT (BaseM MemGC) Imm
                                                             (VariantT
                                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                 (SerT
                                                                   (RefT
                                                                     (BaseM MemGC) Imm
                                                                     (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 2);
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT
                                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (ProdT
                                                             [ (SerT (VarT 0));
                                                               (SerT
                                                                 (CodeRefT
                                                                   (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                       (SerT
                                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (RefT (BaseM MemGC) Imm
                                                             (VariantT
                                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                 (SerT
                                                                   (RefT
                                                                     (BaseM MemGC) Imm
                                                                     (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                      (MonoFunT
                                        [ (VarT 2);
                                          (RefT (BaseM MemGC) Imm
                                            (ProdT
                                              [ (SerT
                                                (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (VALTYPE (AtomR PtrR) GCRefs)
                                                  (RefT (BaseM MemGC) Imm
                                                    (ProdT
                                                      [ (SerT (VarT 0));
                                                        (SerT
                                                          (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                (SerT
                                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (RefT (BaseM MemGC) Imm
                                                      (VariantT
                                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                          (SerT
                                                            (RefT (BaseM MemGC) Imm
                                                              (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                        [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (VariantT
                                              [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 2);
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT
                                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (ProdT
                                                             [ (SerT (VarT 0));
                                                               (SerT
                                                                 (CodeRefT
                                                                   (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                       (SerT
                                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (RefT (BaseM MemGC) Imm
                                                             (VariantT
                                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                 (SerT
                                                                   (RefT
                                                                     (BaseM MemGC) Imm
                                                                     (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 2);
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT
                                                       (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (ProdT
                                                             [ (SerT (VarT 0));
                                                               (SerT
                                                                 (CodeRefT
                                                                   (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                       (SerT
                                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (RefT (BaseM MemGC) Imm
                                                             (VariantT
                                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                                 (SerT
                                                                   (RefT
                                                                     (BaseM MemGC) Imm
                                                                     (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                               [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (VariantT
                                                     [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                       (SerT
                                                         (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))
                                 (coderef
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                     (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 2);
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT
                                                 (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (ProdT
                                                       [ (SerT (VarT 0));
                                                         (SerT
                                                           (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                 (SerT
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (BaseM MemGC) Imm
                                                       (VariantT
                                                         [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                           (SerT
                                                             (RefT (BaseM MemGC) Imm
                                                               (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                         [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (VariantT
                                               [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                 (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
          local.set 4 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (VarT 2);
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT
                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (ProdT
                                                [ (SerT (VarT 0));
                                                  (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                          (SerT
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                         -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
          local.set 5 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (VarT 2);
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT
                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (ProdT
                                                [ (SerT (VarT 0));
                                                  (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                          (SerT
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
          cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
          coderef 1 ;; [] -> [(coderef ((ref (base gc) imm (struct)) i31 -> i31))]
          group ;; [(ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31))] ->
                   [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))]
          new ;; [(prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))] ->
                 [(ref (base gc) imm
                    (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
          cast ;; [(ref (base gc) imm
                     (ser (prod (ref (base gc) imm (struct)) (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (ref (base gc) imm (struct))) (ser (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
          pack ;; [(ref (base gc) imm
                     (struct (ser (ref (base gc) imm (struct))) (ser (coderef ((ref (base gc) imm (struct)) i31 -> i31)))))]
                  ->
                  [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                     (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
          num_const 1 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          num_const 2 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
          cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
          inject_new 0 ;; [(ref (base gc) imm (struct))] ->
                          [(ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser
                                 (ref (base gc) imm
                                   (struct (ser i31)
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
          fold ;; [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser i31)
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          group ;; [i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
                   ->
                   [(prod i31
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
          new ;; [(prod i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
                 ->
                 [(ref (base gc) imm
                    (ser
                      (prod i31
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          cast ;; [(ref (base gc) imm
                     (ser
                       (prod i31
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser i31)
                       (ser
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          inject_new 1 ;; [(ref (base gc) imm
                             (struct (ser i31)
                               (ser
                                 (rec (val ptr gcrefs)
                                   (ref (base gc) imm
                                     (variant (ser (ref (base gc) imm (struct)))
                                       (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                          ->
                          [(ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser
                                 (ref (base gc) imm
                                   (struct (ser i31)
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
          fold ;; [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser i31)
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          group ;; [i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
                   ->
                   [(prod i31
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
          new ;; [(prod i31
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
                 ->
                 [(ref (base gc) imm
                    (ser
                      (prod i31
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          cast ;; [(ref (base gc) imm
                     (ser
                       (prod i31
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser i31)
                       (ser
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          inject_new 1 ;; [(ref (base gc) imm
                             (struct (ser i31)
                               (ser
                                 (rec (val ptr gcrefs)
                                   (ref (base gc) imm
                                     (variant (ser (ref (base gc) imm (struct)))
                                       (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                          ->
                          [(ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser
                                 (ref (base gc) imm
                                   (struct (ser i31)
                                     (ser
                                       (rec (val ptr gcrefs)
                                         (ref (base gc) imm
                                           (variant (ser (ref (base gc) imm (struct)))
                                             (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
          fold ;; [(ref (base gc) imm
                     (variant (ser (ref (base gc) imm (struct)))
                       (ser
                         (ref (base gc) imm
                           (struct (ser i31)
                             (ser
                               (rec (val ptr gcrefs)
                                 (ref (base gc) imm
                                   (variant (ser (ref (base gc) imm (struct)))
                                     (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (base gc) imm
                       (variant (ser (ref (base gc) imm (struct)))
                         (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          group ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
                   ->
                   [(prod
                      (exists.type (val ptr gcrefs) (val ptr gcrefs)
                        (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                      (rec (val ptr gcrefs)
                        (ref (base gc) imm
                          (variant (ser (ref (base gc) imm (struct)))
                            (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
          new ;; [(prod
                    (exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                    (rec (val ptr gcrefs)
                      (ref (base gc) imm
                        (variant (ser (ref (base gc) imm (struct)))
                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))]
                 ->
                 [(ref (base gc) imm
                    (ser
                      (prod
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                        (rec (val ptr gcrefs)
                          (ref (base gc) imm
                            (variant (ser (ref (base gc) imm (struct)))
                              (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          cast ;; [(ref (base gc) imm
                     (ser
                       (prod
                         (exists.type (val ptr gcrefs) (val ptr gcrefs)
                           (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
                  ->
                  [(ref (base gc) imm
                     (struct
                       (ser
                         (exists.type (val ptr gcrefs) (val ptr gcrefs)
                           (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                       (ser
                         (rec (val ptr gcrefs)
                           (ref (base gc) imm
                             (variant (ser (ref (base gc) imm (struct)))
                               (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
          copy ;; [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                         (MonoFunT
                           [ (VarT 2);
                             (RefT (BaseM MemGC) Imm
                               (ProdT
                                 [ (SerT
                                   (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT (VarT 0));
                                           (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                   (SerT
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                           [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                  ->
                  [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                         (MonoFunT
                           [ (VarT 2);
                             (RefT (BaseM MemGC) Imm
                               (ProdT
                                 [ (SerT
                                   (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT (VarT 0));
                                           (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                   (SerT
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                           [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))
                   (coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                         (MonoFunT
                           [ (VarT 2);
                             (RefT (BaseM MemGC) Imm
                               (ProdT
                                 [ (SerT
                                   (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT (VarT 0));
                                           (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                   (SerT
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                           [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
          local.set 5 ;; [(coderef
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (VarT 2);
                                    (RefT (BaseM MemGC) Imm
                                      (ProdT
                                        [ (SerT
                                          (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                            (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (ProdT
                                                [ (SerT (VarT 0));
                                                  (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                          (SerT
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (VariantT
                                                  [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                    (SerT
                                                      (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                  [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (BaseM MemGC) Imm
                                      (VariantT
                                        [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                          (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                         -> []
          inst (type i31) ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 2);
                                        (RefT (BaseM MemGC) Imm
                                          (ProdT
                                            [ (SerT
                                              (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (ProdT
                                                    [ (SerT (VarT 0));
                                                      (SerT
                                                        (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                              (SerT
                                                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (RefT (BaseM MemGC) Imm
                                                    (VariantT
                                                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                        (SerT
                                                          (RefT (BaseM MemGC) Imm
                                                            (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                      [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (BaseM MemGC) Imm
                                          (VariantT
                                            [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                              (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                             ->
                             [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RefT (BaseM MemGC) Imm
                                        (ProdT
                                          [ (SerT
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                              (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT (VarT 0));
                                                    (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); I31T] [ (VarT 1)]))))]))));
                                            (SerT
                                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (VariantT
                                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT I31T); (SerT (VarT 0))])))]))))]))]
                                    [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))]
          inst (type i31) ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RefT (BaseM MemGC) Imm
                                        (ProdT
                                          [ (SerT
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                              (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (BaseM MemGC) Imm
                                                (ProdT
                                                  [ (SerT (VarT 0));
                                                    (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); I31T] [ (VarT 1)]))))]))));
                                            (SerT
                                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (BaseM MemGC) Imm
                                                  (VariantT
                                                    [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                      (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT I31T); (SerT (VarT 0))])))]))))]))]
                                    [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (BaseM MemGC) Imm
                                        (VariantT
                                          [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                            (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))]
                             ->
                             [(coderef
                                ((var 0)
                                (ref (base gc) imm
                                  (struct
                                    (ser
                                      (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                        (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                    (ser
                                      (rec (val ptr gcrefs)
                                        (ref (base gc) imm
                                          (variant (ser (ref (base gc) imm (struct)))
                                            (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))
                                ->
                                (rec (val ptr gcrefs)
                                  (ref (base gc) imm
                                    (variant (ser (ref (base gc) imm (struct)))
                                      (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))]
          call_indirect ;; [(var 0)
                            (ref (base gc) imm
                              (struct
                                (ser
                                  (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                    (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                (ser
                                  (rec (val ptr gcrefs)
                                    (ref (base gc) imm
                                      (variant (ser (ref (base gc) imm (struct)))
                                        (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))
                            (coderef
                              ((var 0)
                              (ref (base gc) imm
                                (struct
                                  (ser
                                    (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                      (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                  (ser
                                    (rec (val ptr gcrefs)
                                      (ref (base gc) imm
                                        (variant (ser (ref (base gc) imm (struct)))
                                          (ser (ref (base gc) imm (struct (ser i31) (ser (var 0)))))))))))
                              ->
                              (rec (val ptr gcrefs)
                                (ref (base gc) imm
                                  (variant (ser (ref (base gc) imm (struct)))
                                    (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))))]
                           ->
                           [(rec (val ptr gcrefs)
                              (ref (base gc) imm
                                (variant (ser (ref (base gc) imm (struct)))
                                  (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 2);
                                         (RefT (BaseM MemGC) Imm
                                           (ProdT
                                             [ (SerT
                                               (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (BaseM MemGC) Imm
                                                   (ProdT
                                                     [ (SerT (VarT 0));
                                                       (SerT
                                                         (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                               (SerT
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (BaseM MemGC) Imm
                                                     (VariantT
                                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                         (SerT
                                                           (RefT (BaseM MemGC) Imm
                                                             (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                       [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (BaseM MemGC) Imm
                                           (VariantT
                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                               (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
          drop ;; [(coderef
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                         (MonoFunT
                           [ (VarT 2);
                             (RefT (BaseM MemGC) Imm
                               (ProdT
                                 [ (SerT
                                   (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                     (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (BaseM MemGC) Imm
                                       (ProdT
                                         [ (SerT (VarT 0));
                                           (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                   (SerT
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (BaseM MemGC) Imm
                                         (VariantT
                                           [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                             (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                           [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (BaseM MemGC) Imm
                               (VariantT
                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                   (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 2);
                                               (RefT (BaseM MemGC) Imm
                                                 (ProdT
                                                   [ (SerT
                                                     (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (VALTYPE (AtomR PtrR) GCRefs)
                                                       (RefT (BaseM MemGC) Imm
                                                         (ProdT
                                                           [ (SerT (VarT 0));
                                                             (SerT
                                                               (CodeRefT
                                                                 (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                                     (SerT
                                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (RefT (BaseM MemGC) Imm
                                                           (VariantT
                                                             [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                               (SerT
                                                                 (RefT (BaseM MemGC) Imm
                                                                   (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                             [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (BaseM MemGC) Imm
                                                 (VariantT
                                                   [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                     (SerT
                                                       (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser
                         (coderef
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (VarT 2);
                                   (RefT (BaseM MemGC) Imm
                                     (ProdT
                                       [ (SerT
                                         (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                           (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (BaseM MemGC) Imm
                                             (ProdT
                                               [ (SerT (VarT 0));
                                                 (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                         (SerT
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (BaseM MemGC) Imm
                                               (VariantT
                                                 [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                   (SerT
                                                     (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                 [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (BaseM MemGC) Imm
                                     (VariantT
                                       [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                         (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))])))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm
                    (struct (ser (var 0))
                      (ser
                        (coderef
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 2);
                                  (RefT (BaseM MemGC) Imm
                                    (ProdT
                                      [ (SerT
                                        (ExistsTypeT (VALTYPE (AtomR PtrR) GCRefs)
                                          (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (BaseM MemGC) Imm
                                            (ProdT
                                              [ (SerT (VarT 0));
                                                (SerT (CodeRefT (InnerFunT (MonoFunT [ (VarT 0); (VarT 2)] [ (VarT 1)]))))]))));
                                        (SerT
                                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                            (RefT (BaseM MemGC) Imm
                                              (VariantT
                                                [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                                  (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 2)); (SerT (VarT 0))])))]))))]))]
                                [ (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (BaseM MemGC) Imm
                                    (VariantT
                                      [ (SerT (RefT (BaseM MemGC) Imm (ProdT [])));
                                        (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))])))])))]))))))))]
               ->
               [(rec (val ptr gcrefs)
                  (ref (base gc) imm
                    (variant (ser (ref (base gc) imm (struct))) (ser (ref (base gc) imm (struct (ser i31) (ser (var 0))))))))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1 2)
      (export "map" (func 0))
      (export "_start" (func 2)))
    -----------poly_id_apply-----------
    (module
      (func (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))
          (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 0 ;; [] ->
                     [(coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (var 0)]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))] [6 => (plug (prod i32))])
          local.set 2 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 2 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 2 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 3 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.get move 2 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 2 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 6 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 4 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [(var 1)]
          copy ;; [(var 1)] -> [(var 1) (var 1)]
          local.set 1 ;; [(var 1)] -> []
          local.get move 6 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] ->
                  [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 6 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type (var 1)) ;; [(coderef
                                    (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                                 -> [(coderef ((var 0) (var 1) -> (var 1)))]
          call_indirect ;; [(var 0) (var 1) (coderef ((var 0) (var 1) -> (var 1)))] -> [(var 1)]
          local.get move 6 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] -> []
          local.get move 4 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 2 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm
                    (struct (ser (var 0))
                      (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [(var 0)]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod)]
        new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
        cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
        coderef 1 ;; [] ->
                     [(coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
        group ;; [(ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)])))]
                 ->
                 [(prod (ref (base gc) imm (struct))
                    (coderef
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
        new ;; [(prod (ref (base gc) imm (struct))
                  (coderef
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct))
                      (coderef
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct))
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct)))
                     (ser
                       (coderef
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT [ (RefT (BaseM MemGC) Imm (ProdT [])); (VarT 0)] [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => (plug (prod i32))]
                 [2 => (plug (prod i32))] [3 => (plug (prod i32))] [4 => (plug (prod i32))]
                 [5 => (plug (prod i32))])
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (base gc) imm
                            (struct (ser (var 0))
                              (ser
                                (coderef
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 4 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] ->
                  [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type i31) ;; [(coderef
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                             -> [(coderef ((var 0) i31 -> i31))]
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> i31))] -> [i31]
          local.get move 5 ;; [] ->
                              [(coderef
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0))
                                   (ser
                                     (coderef
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (base gc) imm
                     (struct (ser (var 0))
                       (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm
                    (struct (ser (var 0))
                      (ser (coderef (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [i31]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1 2)
      (export "id" (func 0))
      (export "apply" (func 1))
      (export "_start" (func 2)))
    -----------mini_zip-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
              (MonoFunT
                [ (RefT (BaseM MemGC) Imm (ProdT []));
                  (RefT (BaseM MemGC) Imm
                    (ProdT
                      [ (SerT (RefT (BaseM MemGC) Mut (SerT (VarT 1)))); (SerT (RefT (BaseM MemGC) Mut (SerT (VarT 0))))]))]
                [ (RefT (BaseM MemGC) Mut (SerT (RefT (BaseM MemGC) Imm (ProdT [ (SerT (VarT 1)); (SerT (VarT 0))]))))])))
          (local ptr ptr ptr ptr)
        local.get move 1 ;; [] ->
                            [(ref (base gc) imm
                               (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
        copy ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))
                 (ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
        local.set 1 ;; [(ref (base gc) imm
                          (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                       -> []
        load (path 0) copy ;; [(ref (base gc) imm
                                 (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                              ->
                              [(ref (base gc) imm
                                 (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))
                               (ref (base gc) mut (ser (var 1)))]
        local.set 2 ;; [(ref (base gc) mut (ser (var 1)))] -> []
        drop ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                -> []
        local.get move 2 ;; [] -> [(ref (base gc) mut (ser (var 1)))]
        load (path) copy ;; [(ref (base gc) mut (ser (var 1)))] -> [(ref (base gc) mut (ser (var 1))) (var 1)]
        local.set 3 ;; [(var 1)] -> []
        drop ;; [(ref (base gc) mut (ser (var 1)))] -> []
        local.get move 3 ;; [] -> [(var 1)]
        local.get move 1 ;; [] ->
                            [(ref (base gc) imm
                               (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
        copy ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))
                 (ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
        local.set 1 ;; [(ref (base gc) imm
                          (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                       -> []
        load (path 1) copy ;; [(ref (base gc) imm
                                 (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                              ->
                              [(ref (base gc) imm
                                 (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))
                               (ref (base gc) mut (ser (var 0)))]
        local.set 4 ;; [(ref (base gc) mut (ser (var 0)))] -> []
        drop ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                -> []
        local.get move 4 ;; [] -> [(ref (base gc) mut (ser (var 0)))]
        load (path) copy ;; [(ref (base gc) mut (ser (var 0)))] -> [(ref (base gc) mut (ser (var 0))) (var 0)]
        local.set 5 ;; [(var 0)] -> []
        drop ;; [(ref (base gc) mut (ser (var 0)))] -> []
        local.get move 5 ;; [] -> [(var 0)]
        group ;; [(var 1) (var 0)] -> [(prod (var 1) (var 0))]
        new ;; [(prod (var 1) (var 0))] -> [(ref (base gc) imm (ser (prod (var 1) (var 0))))]
        cast ;; [(ref (base gc) imm (ser (prod (var 1) (var 0))))] ->
                [(ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))]
        new ;; [(ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))] ->
               [(ref (base gc) mut (ser (ref (base gc) imm (struct (ser (var 1)) (ser (var 0))))))]
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> []
        local.get move 1 ;; [] ->
                            [(ref (base gc) imm
                               (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
        drop ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) mut (ser (var 1)))) (ser (ref (base gc) mut (ser (var 0))))))]
                -> [])
      (table 0)
      (export "mini_zip" (func 0)))
    -----------closure_simpl-----------
    (module
      (func ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31) (local ptr ptr)
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct (ser i31)))]
        copy ;; [(ref (base gc) imm (struct (ser i31)))] ->
                [(ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct (ser i31)))]
        local.set 0 ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        load (path 0) copy ;; [(ref (base gc) imm (struct (ser i31)))] -> [(ref (base gc) imm (struct (ser i31))) i31]
        local.set 2 ;; [i31] -> []
        drop ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        local.get move 2 ;; [] -> [i31]
        local.set 3 ;; [i31] -> []
        local.get move 3 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 3 ;; [i31] -> []
        local.get move 3 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct (ser i31)))]
        drop ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        local.get move 1 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.set 1 ;; [i31] -> []
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        group ;; [i31] -> [(prod i31)]
        new ;; [(prod i31)] -> [(ref (base gc) imm (ser (prod i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31)))] -> [(ref (base gc) imm (struct (ser i31)))]
        coderef 0 ;; [] -> [(coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31))]
        group ;; [(ref (base gc) imm (struct (ser i31)))
                  (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31))]
                 ->
                 [(prod (ref (base gc) imm (struct (ser i31)))
                    (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct (ser i31)))
                  (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct (ser i31)))
                      (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct (ser i31)))
                       (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct (ser i31))))
                     (ser (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct (ser i31))))
                     (ser (coderef ((ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct)) -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
                       -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
                       -> []
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => i31]
                 [2 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
                 [3 => (plug (prod i32))] [4 => (plug (prod i32))] [5 => (plug (prod i32))]
                 [6 => (plug (prod i32))] [7 => (plug (prod i32))])
          local.set 3 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          local.get move 3 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          local.set 3 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          load (path 0) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                                 (var 0)]
          local.set 4 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
          local.get move 4 ;; [] -> [(var 0)]
          local.set 5 ;; [(var 0)] -> []
          local.get move 3 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          local.set 3 ;; [(ref (base gc) imm
                            (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                         -> []
          load (path 1) copy ;; [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                                ->
                                [(ref (base gc) imm
                                   (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))
                                 (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 6 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
          local.get move 6 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 7 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          local.get move 5 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 5 ;; [(var 0)] -> []
          group ;; [] -> [(prod)]
          new ;; [(prod)] -> [(ref (base gc) imm (ser (prod)))]
          cast ;; [(ref (base gc) imm (ser (prod)))] -> [(ref (base gc) imm (struct))]
          local.get move 7 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          copy ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] ->
                  [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))
                   (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          local.set 7 ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          call_indirect ;; [(var 0) (ref (base gc) imm (struct)) (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
                           -> [i31]
          local.get move 7 ;; [] -> [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))]
          drop ;; [(coderef ((var 0) (ref (base gc) imm (struct)) -> i31))] -> []
          local.get move 5 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 3 ;; [] ->
                              [(ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31)))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
               -> [i31]
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm
                                 (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) (ref (base gc) imm (struct)) -> i31))))))]
                -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------closure_complex-----------
    (module
      (func
          ((ref (base gc) imm
             (struct
               (ser
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
               (ser i31)))
          i31 -> i31) (local ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get move 0 ;; [] ->
                            [(ref (base gc) imm
                               (struct
                                 (ser
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                 (ser i31)))]
        copy ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                ->
                [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))
                 (ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
        local.set 0 ;; [(ref (base gc) imm
                          (struct
                            (ser
                              (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                            (ser i31)))]
                       -> []
        load (path 0) copy ;; [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                   (ser i31)))]
                              ->
                              [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                   (ser i31)))
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        drop ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        local.get move 0 ;; [] ->
                            [(ref (base gc) imm
                               (struct
                                 (ser
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                 (ser i31)))]
        copy ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                ->
                [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))
                 (ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
        local.set 0 ;; [(ref (base gc) imm
                          (struct
                            (ser
                              (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                            (ser i31)))]
                       -> []
        load (path 1) copy ;; [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                   (ser i31)))]
                              ->
                              [(ref (base gc) imm
                                 (struct
                                   (ser
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                   (ser i31)))
                               i31]
        local.set 4 ;; [i31] -> []
        drop ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                -> []
        local.get move 4 ;; [] -> [i31]
        local.set 5 ;; [i31] -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        unpack (localfx
                 [0 =>
                 (ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                 [1 => i31] [2 => (plug (prod i32))]
                 [3 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                 [4 => (plug (prod i32))] [5 => i31] [6 => (plug (prod i32))]
                 [7 => (plug (prod i32))] [8 => (plug (prod i32))] [9 => (plug (prod i32))]
                 [10 => (plug (prod i32))])
          local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 6 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 0) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))) (var 0)]
          local.set 7 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 7 ;; [] -> [(var 0)]
          local.set 8 ;; [(var 0)] -> []
          local.get move 6 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 6 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 1) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                                 (coderef ((var 0) i31 -> i31))]
          local.set 9 ;; [(coderef ((var 0) i31 -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 9 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          local.set 10 ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 8 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 8 ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [i31]
          copy ;; [i31] -> [i31 i31]
          local.set 1 ;; [i31] -> []
          local.get move 10 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          copy ;; [(coderef ((var 0) i31 -> i31))] -> [(coderef ((var 0) i31 -> i31)) (coderef ((var 0) i31 -> i31))]
          local.set 10 ;; [(coderef ((var 0) i31 -> i31))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> i31))] -> [i31]
          local.get move 10 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          drop ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 8 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 6 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
               -> [i31]
        untag ;; [i31] -> [(num i32)]
        local.get move 5 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 5 ;; [i31] -> []
        untag ;; [i31] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 5 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                -> []
        local.get move 0 ;; [] ->
                            [(ref (base gc) imm
                               (struct
                                 (ser
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                                 (ser i31)))]
        drop ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
                -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (func ((ref (base gc) imm (struct (ser i31))) i31 -> i31) (local ptr ptr)
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct (ser i31)))]
        copy ;; [(ref (base gc) imm (struct (ser i31)))] ->
                [(ref (base gc) imm (struct (ser i31))) (ref (base gc) imm (struct (ser i31)))]
        local.set 0 ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        load (path 0) copy ;; [(ref (base gc) imm (struct (ser i31)))] -> [(ref (base gc) imm (struct (ser i31))) i31]
        local.set 2 ;; [i31] -> []
        drop ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        local.get move 2 ;; [] -> [i31]
        local.set 3 ;; [i31] -> []
        local.get move 3 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 3 ;; [i31] -> []
        untag ;; [i31] -> [(num i32)]
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        untag ;; [i31] -> [(num i32)]
        i32.add ;; [(num i32) (num i32)] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.get move 3 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct (ser i31)))]
        drop ;; [(ref (base gc) imm (struct (ser i31)))] -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> [])
      (func ((ref (base gc) imm (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num i32)]
        tag ;; [(num i32)] -> [i31]
        local.set 1 ;; [i31] -> []
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        group ;; [i31] -> [(prod i31)]
        new ;; [(prod i31)] -> [(ref (base gc) imm (ser (prod i31)))]
        cast ;; [(ref (base gc) imm (ser (prod i31)))] -> [(ref (base gc) imm (struct (ser i31)))]
        coderef 1 ;; [] -> [(coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31))]
        group ;; [(ref (base gc) imm (struct (ser i31))) (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31))] ->
                 [(prod (ref (base gc) imm (struct (ser i31)))
                    (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))]
        new ;; [(prod (ref (base gc) imm (struct (ser i31))) (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod (ref (base gc) imm (struct (ser i31)))
                      (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod (ref (base gc) imm (struct (ser i31)))
                       (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct (ser i31))))
                     (ser (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct (ser (ref (base gc) imm (struct (ser i31))))
                     (ser (coderef ((ref (base gc) imm (struct (ser i31))) i31 -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        local.get move 1 ;; [] -> [i31]
        copy ;; [i31] -> [i31 i31]
        local.set 1 ;; [i31] -> []
        group ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                    (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                  i31]
                 ->
                 [(prod
                    (exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                    i31)]
        new ;; [(prod
                  (exists.type (val ptr gcrefs) (val ptr gcrefs)
                    (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                  i31)]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod
                      (exists.type (val ptr gcrefs) (val ptr gcrefs)
                        (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                      i31)))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                       i31)))]
                ->
                [(ref (base gc) imm
                   (struct
                     (ser
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                     (ser i31)))]
        coderef 0 ;; [] ->
                     [(coderef
                        ((ref (base gc) imm
                           (struct
                             (ser
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                             (ser i31)))
                        i31 -> i31))]
        group ;; [(ref (base gc) imm
                    (struct
                      (ser
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                      (ser i31)))
                  (coderef
                    ((ref (base gc) imm
                       (struct
                         (ser
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                         (ser i31)))
                    i31 -> i31))]
                 ->
                 [(prod
                    (ref (base gc) imm
                      (struct
                        (ser
                          (exists.type (val ptr gcrefs) (val ptr gcrefs)
                            (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                        (ser i31)))
                    (coderef
                      ((ref (base gc) imm
                         (struct
                           (ser
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                           (ser i31)))
                      i31 -> i31)))]
        new ;; [(prod
                  (ref (base gc) imm
                    (struct
                      (ser
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                      (ser i31)))
                  (coderef
                    ((ref (base gc) imm
                       (struct
                         (ser
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                         (ser i31)))
                    i31 -> i31)))]
               ->
               [(ref (base gc) imm
                  (ser
                    (prod
                      (ref (base gc) imm
                        (struct
                          (ser
                            (exists.type (val ptr gcrefs) (val ptr gcrefs)
                              (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                          (ser i31)))
                      (coderef
                        ((ref (base gc) imm
                           (struct
                             (ser
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                             (ser i31)))
                        i31 -> i31)))))]
        cast ;; [(ref (base gc) imm
                   (ser
                     (prod
                       (ref (base gc) imm
                         (struct
                           (ser
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                           (ser i31)))
                       (coderef
                         ((ref (base gc) imm
                            (struct
                              (ser
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                              (ser i31)))
                         i31 -> i31)))))]
                ->
                [(ref (base gc) imm
                   (struct
                     (ser
                       (ref (base gc) imm
                         (struct
                           (ser
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                           (ser i31))))
                     (ser
                       (coderef
                         ((ref (base gc) imm
                            (struct
                              (ser
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                              (ser i31)))
                         i31 -> i31)))))]
        pack ;; [(ref (base gc) imm
                   (struct
                     (ser
                       (ref (base gc) imm
                         (struct
                           (ser
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                           (ser i31))))
                     (ser
                       (coderef
                         ((ref (base gc) imm
                            (struct
                              (ser
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))))
                              (ser i31)))
                         i31 -> i31)))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                       -> []
        unpack (localfx [0 => (ref (base gc) imm (struct))] [1 => i31]
                 [2 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                 [3 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                 [4 => (plug (prod i32))] [5 => (plug (prod i32))] [6 => (plug (prod i32))]
                 [7 => (plug (prod i32))] [8 => (plug (prod i32))])
          local.set 4 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 4 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 4 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 0) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))) (var 0)]
          local.set 5 ;; [(var 0)] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 5 ;; [] -> [(var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.get move 4 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                  [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          local.set 4 ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          load (path 1) copy ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] ->
                                [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))
                                 (coderef ((var 0) i31 -> i31))]
          local.set 7 ;; [(coderef ((var 0) i31 -> i31))] -> []
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
          local.get move 7 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          local.set 8 ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 6 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num i32)]
          tag ;; [(num i32)] -> [i31]
          local.get move 8 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          copy ;; [(coderef ((var 0) i31 -> i31))] -> [(coderef ((var 0) i31 -> i31)) (coderef ((var 0) i31 -> i31))]
          local.set 8 ;; [(coderef ((var 0) i31 -> i31))] -> []
          call_indirect ;; [(var 0) i31 (coderef ((var 0) i31 -> i31))] -> [i31]
          local.get move 8 ;; [] -> [(coderef ((var 0) i31 -> i31))]
          drop ;; [(coderef ((var 0) i31 -> i31))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 4 ;; [] -> [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))]
          drop ;; [(ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31)))))] -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
               -> [i31]
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (base gc) imm (struct (ser (var 0)) (ser (coderef ((var 0) i31 -> i31))))))]
                -> []
        local.get move 1 ;; [] -> [i31]
        drop ;; [i31] -> []
        local.get move 0 ;; [] -> [(ref (base gc) imm (struct))]
        drop ;; [(ref (base gc) imm (struct))] -> [])
      (table 0 1 2)
      (export "_start" (func 2)))
    |xxx}]
