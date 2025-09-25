open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open! Richwasm_common

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
      (func (->)
        i32.const 1)
      (table)
      { me_name = "_start"; me_desc = (ExFunction 0) }) |}];
  next ();
  [%expect
    {|
    ((m_imports ()) (m_globals ())
     (m_funcs
      (((mf_type (MonoFunT (InstrT () ())))
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))) 1))))))
     (m_table ()) (m_start ())
     (m_exports (((me_name _start) (me_desc (ExFunction 0)))))) |}]
