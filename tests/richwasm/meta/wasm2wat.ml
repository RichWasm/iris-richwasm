open! Core
open! Core_unix
open! Stdlib.Format

let wasm2wat ?(check = true) (wasm : string) : (string, string) Result.t =
  let Core_unix.Process_info.{ pid; stdin; stdout; stderr } =
    let show_nicely = false in
    let extra_args =
      if show_nicely then
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
    Core_unix.create_process ~prog:"wasm2wat"
      ~args:([ "--enable-multi-memory" ] @ extra_args @ should_check @ [ "-" ])
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

let pp_as_wat ?(check = true) ff (wasm : string) =
  match wasm2wat ~check wasm with
  | Ok out -> fprintf ff "%s" out
  | Error err -> fprintf ff "wasm2wat Error: %s" err
