open! Core
open! Core_unix

let () =
  let rw_runtime_path = Sys.getenv_exn "RW_RUNTIME_WASM_PATH" in
  let host_runtime_path = Sys.getenv_exn "WASM_HOST_RUNTIME_PATH" in
  Test_e2e.Main.run rw_runtime_path host_runtime_path
