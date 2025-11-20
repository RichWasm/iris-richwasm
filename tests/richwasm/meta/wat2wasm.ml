open! Core
open! Core_unix
open! Stdlib.Format

let wat2wasm (wasm : string) : (string, string) Result.t =
  let Core_unix.Process_info.{ pid; stdin; stdout; stderr } =
    Core_unix.create_process ~prog:"wat2wasm"
      ~args:[ "--enable-multi-memory"; "--output=-"; "-" ]
  in
  let oc = Core_unix.out_channel_of_descr stdin in
  Out_channel.output_string oc wasm;
  Out_channel.flush oc;
  Out_channel.close oc;

  let ic_out = Core_unix.in_channel_of_descr stdout in
  let ic_err = Core_unix.in_channel_of_descr stderr in
  let out = In_channel.input_all ic_out in
  let err = In_channel.input_all ic_err in
  In_channel.close ic_out;
  In_channel.close ic_err;

  (* TODO: this should probably be async *)
  match Core_unix.waitpid pid with
  | Ok () -> Ok (out ^ err)
  | Error _ -> Error (out ^ err)

let pp_as_wasm ff (wasm : string) =
  match wat2wasm wasm with
  | Ok out -> fprintf ff "%s" out
  | Error err -> fprintf ff "wat2wasm Error: %s" err
