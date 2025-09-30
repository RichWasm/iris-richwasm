open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
module RichWasm = Richwasm_common.Syntax

let pipline x =
  x
  |> Index.Compile.compile_module
  |> ( function
  | Ok x -> x
  | Error err -> failwith @@ asprintf "%a" Index.Err.pp err )
  |> Cc.Compile.compile_module
  |> ( function
  | Ok x -> x
  | Error err -> failwith @@ asprintf "%a" Cc.Compile.Err.pp err )
  |> Codegen.Compile.compile_module
  |> function
  | Ok x -> x
  | Error err -> failwith @@ Codegen.Err.to_string err

let spipline s = s |> Parse.from_string_exn |> pipline

let%expect_test "basic functionality" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let suspended = ref (fun () -> ()) in

  let run (s : string) =
    try
      let x = s |> spipline in
      printf "%a" RichWasm.Module.pp x;
      suspended := fun () -> printf "%a" RichWasm.Module.pp_sexp x
    with Failure msg ->
      printf "Failure: %s" msg;
      suspended := fun () -> printf "Failure ^^^"
  in

  let next () =
    !suspended ();
    suspended := fun () -> ()
  in

  run {| 1 |};
  [%expect
    {|
    (module
      (func -> (Num i32)
        i32.const 1)
      (table)
      (export _start (func 0))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (globals ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1))))))
     (table ()) (start ()) (exports (((name _start) (desc (ExFunction 0)))))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect {|
    (module
      (func -> (Prod [(Num i32); (Num i32); (Num i32); (Num i32)])
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        (Group 4))
      (table)
      (export _start (func 0))) |}];
  next ();
  [%expect {|
    ((imports ()) (globals ())
     (functions
      (((typ
         (FunctionType () ()
          ((Prod ((Num (Int I32)) (Num (Int I32)) (Num (Int I32)) (Num (Int I32)))))))
        (locals ())
        (body
         ((NumConst (Int I32) 1) (NumConst (Int I32) 2) (NumConst (Int I32) 3)
          (NumConst (Int I32) 4) (Group 4))))))
     (table ()) (start ()) (exports (((name _start) (desc (ExFunction 0)))))) |}];

  run {| (1 + 2) |};
  [%expect {|
    (module
      (func -> (Num i32)
        i32.const 1
        i32.const 2
        i32.add)
      (table)
      (export _start (func 0))) |}];
  next ();
  [%expect {|
    ((imports ()) (globals ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1) (NumConst (Int I32) 2) (Num (Int2 I32 Add)))))))
     (table ()) (start ()) (exports (((name _start) (desc (ExFunction 0)))))) |}];

  ()

let%expect_test "examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         try
           m
           |> pipline
           |> printf "-----------%s-----------@.%a@." n RichWasm.Module.pp
         with Failure msg -> printf "-----------%s-----------@.%s@." n msg);
  [%expect
    {|
    -----------simple_app_lambda-----------
    Function named lam_1 is not mapped in env: ((global_map ())
                                                (function_map ()))
    -----------add_one_program-----------
    Function named add-one is not mapped in env: ((global_map ())
                                                  (function_map ()))
    -----------add_tup_ref-----------
    TODO
    -----------print_10-----------
    Function named print is not mapped in env: ((global_map ())
                                                (function_map ()))
    -----------factorial_program-----------
    Function named factorial is not mapped in env: ((global_map ())
                                                    (function_map ()))
    -----------safe_div-----------
    TODO
    -----------incr_n-----------
    TODO
    -----------fix_factorial-----------
    TODO |}]
