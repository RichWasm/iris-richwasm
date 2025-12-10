open! Core
open! Core_unix
open! Stdlib.Format

let wat2wasm ?(check = true) (wasm : string) : (string, string) Result.t =
  let args = [ "--enable-multi-memory"; "--output=-"; "-" ] in
  let args = if check then args else "--no-check" :: args in
  Utils.Process_capture.run_concat ~input:wasm ~prog:"wat2wasm" ~args ()

let pp_as_wasm ff (wasm : string) =
  match wat2wasm wasm with
  | Ok out -> fprintf ff "%s" out
  | Error err -> fprintf ff "wat2wasm Error: %s" err
