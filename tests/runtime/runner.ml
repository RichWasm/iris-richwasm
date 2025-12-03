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
      [ 0, 4, 8, 10 ]
      mmmem size 65536
      mmalloc 16384 (one whole page)
      12
      mmmem size 131072
      ---
      original gcmem size 65536
      gcalloc 4 65537
      gcmem size 131072
      gcalloc tests, allocate 4, 1, 2
      [ 65541, 65545, 65547 ]
      gcmem size 131072
      gcalloc 65536 (four pages)
      65549
      gcmem size 393216
      ---
      make sure mmmem hasn't changed when working with gc: true
      ---
      registerroot: numbers should just incrememnt by 4
      [ 0, 4, 8, 12 ]
      ---
      tableset
      set index 1, check length
      2
      set index 0, check length
      2
      now set index 8
      9
      index 8 should be gcalloc, call it (ptr should be >100k)
      131085
      ---
      make sure free, setflag, and unregisterroot don't trap
      ---
    |}]
