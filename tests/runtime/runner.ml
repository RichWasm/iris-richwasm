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
      mmalloc tests, allocate 4, 4, 1, 2
      [ 1, 17, 33, 37 ]
      mmmem size 65536
      mmalloc 16384 (one whole page)
      45
      mmmem size 131072
      ---
      original gcmem size 65536
      gcalloc 4 65535
      gcmem size 131072
      gcalloc tests, allocate 4, 1, 2
      [ 65551, 65567, 65571 ]
      gcmem size 131072
      gcalloc 65536 (four pages)
      65579
      gcmem size 393216
      ---
      make sure mmmem hasn't changed when working with gc: true
      ---
      registerroot: numbers should just incrememnt by 4
      [ 3, 7, 11, 15 ]
      ---
      make sure free, setflag, and unregisterroot don't trap
      ---
    |}]
