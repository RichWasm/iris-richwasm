open! Core
open! Core_unix

let () =
  let rw_runtime = Sys.getenv_exn "RW_RUNTIME_WASM_PATH" in
  let host_single = Sys.getenv_exn "HOST_SINGLE_PATH" in
  let host_triple = Sys.getenv_exn "HOST_TRIPLE_PATH" in
  Test_e2e.Main.(run { rw_runtime; host_single; host_triple })
