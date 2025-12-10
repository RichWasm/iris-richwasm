open! Core
open! Core_unix
open Richwasm_common.Monads

module Process_capture = struct
  module Output = struct
    type t = {
      stdout : string;
      stderr : string;
    }
  end

  let run ?input ?(env = `Extend []) ~prog ~args () : Output.t ResultM(Output).t
      =
    let Core_unix.Process_info.{ pid; stdin; stdout; stderr } =
      Core_unix.create_process_env ~prog ~args ~env ()
    in

    let oc = Core_unix.out_channel_of_descr stdin in
    Option.iter input ~f:(fun s ->
        Out_channel.output_string oc s;
        Out_channel.flush oc);
    Out_channel.close oc;

    let ic_out = Core_unix.in_channel_of_descr stdout in
    let ic_err = Core_unix.in_channel_of_descr stderr in
    let out = In_channel.input_all ic_out in
    let err = In_channel.input_all ic_err in
    In_channel.close ic_out;
    In_channel.close ic_err;

    match Core_unix.waitpid pid with
    | Ok () -> Ok { stdout = out; stderr = err }
    | Error _ -> Error { stdout = out; stderr = err }

  let run_concat ?input ?env ~prog ~args () : String.t ResultM(String).t =
    match run ?input ?env ~prog ~args () with
    | Ok { stdout; stderr } -> Ok (stdout ^ stderr)
    | Error { stdout; stderr } -> Error (stdout ^ stderr)
end
