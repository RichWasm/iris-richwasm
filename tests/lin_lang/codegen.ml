open! Base
open! Stdlib.Format
open! Richwasm_lin_lang

module RichWasm = Richwasm_common.Syntax

let%expect_test "basic functionality" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let suspended = ref (fun () -> ()) in

  let run (s : string) =
    try
      let x =
        s
        |> Parse.from_string_exn
        |> Index.Compile.compile_module
        |> Cc.Compile.compile_module
        |> ( function
        | Ok x -> x
        | Error err -> failwith @@ Cc.Compile.Err.to_string err )
        |> Codegen.Compile.compile_module
        |> function
        | Ok x -> x
        | Error err -> failwith @@ Codegen.Err.to_string err
      in
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
      (func (-> (Num i32))
        i32.const 1)
      (table)
      { name = "_start"; desc = (ExFunction 0) }) |}];
  next ();
  [%expect
    {|
    ((imports ()) (globals ())
     (functions
      (((typ (FunctionType () (InstructionType () ((Num (Int I32)))))) (locals ())
        (body ((NumConst (Int I32) 1))))))
     (table ()) (start ()) (exports (((name _start) (desc (ExFunction 0)))))) |}]
