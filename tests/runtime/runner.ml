open! Core
open! Core_unix

let run_command cmd =
  let ic = open_process_in cmd in
  let output = In_channel.input_all ic in
  match close_process_in ic with
  | Ok () -> Ok output
  | Error _ as e -> e

let%expect_test "runtime" =
  (match run_command "node ./harness.ts" with
  | Ok out -> print_endline out
  | Error _ -> print_endline "Failed running test harness");
  [%expect
    {|
      [ 0, 4, 8, 9 ]
      [ 65536, 65540, 65544, 65545 ]
      [ 0, 4, 8, 12 ]
    |}]
