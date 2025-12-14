open! Core
open! Core_unix
open! Stdlib.Format

let wasm2wat ?(pretty = false) ?(check = true) (wasm : string) :
    (string, string) Result.t =
  let args =
    let extra_args =
      if pretty then
        [
          "--inline-exports";
          "--inline-imports";
          "--generate-names";
          "--fold-exprs";
        ]
      else
        []
    in
    let should_check = if check then [] else [ "--no-check" ] in
    [ "--enable-multi-memory" ] @ extra_args @ should_check @ [ "-" ]
  in
  Utils.Process_capture.run_concat ~input:wasm ~prog:"wasm2wat" ~args ()

let pp_as_wat ?pretty ?check ff (wasm : string) =
  match wasm2wat ?pretty ?check wasm with
  | Ok out -> fprintf ff "%s" out
  | Error err -> fprintf ff "wasm2wat Error: %s" err
