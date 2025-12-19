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

module Process_capture_three = struct
  module Output = Process_capture.Output

  (* Spawn child with:
     - stdin  -> fd 0
     - stdout -> fd 1
     - stderr -> fd 2
     - extra inputs -> fd 3,4,5
  *)
  let run ?input ?input1 ?input2 ?input3 ?(env = `Extend []) ~prog ~args () :
      Output.t ResultM(Output).t =
    let mk_pipe () =
      let r, w = Core_unix.pipe () in
      Core_unix.set_close_on_exec r;
      Core_unix.set_close_on_exec w;
      (r, w)
    in

    let stdin_r, stdin_w = mk_pipe () in
    let stdout_r, stdout_w = mk_pipe () in
    let stderr_r, stderr_w = mk_pipe () in

    let in1_r, in1_w = mk_pipe () in
    let in2_r, in2_w = mk_pipe () in
    let in3_r, in3_w = mk_pipe () in

    match Core_unix.fork () with
    | `In_the_child ->
        let dup2_keep ~src ~dst =
          Core_unix.dup2 ~src ~dst ~close_on_exec:false ()
        in
        Core_unix.close stdin_w;
        Core_unix.close stdout_r;
        Core_unix.close stderr_r;
        Core_unix.close in1_w;
        Core_unix.close in2_w;
        Core_unix.close in3_w;

        dup2_keep ~src:stdin_r ~dst:Core_unix.stdin;
        dup2_keep ~src:stdout_w ~dst:Core_unix.stdout;
        dup2_keep ~src:stderr_w ~dst:Core_unix.stderr;

        let fd3 = Core_unix.File_descr.of_int 3 in
        let fd4 = Core_unix.File_descr.of_int 4 in
        let fd5 = Core_unix.File_descr.of_int 5 in
        dup2_keep ~src:in1_r ~dst:fd3;
        dup2_keep ~src:in2_r ~dst:fd4;
        dup2_keep ~src:in3_r ~dst:fd5;

        List.iter
          [ stdin_r; stdout_w; stderr_w; in1_r; in2_r; in3_r ]
          ~f:Core_unix.close;

        Core_unix.exec ~prog ~argv:(prog :: args) ~env () |> Core.never_returns
    | `In_the_parent pid ->
        Core_unix.close stdin_r;
        Core_unix.close stdout_w;
        Core_unix.close stderr_w;
        Core_unix.close in1_r;
        Core_unix.close in2_r;
        Core_unix.close in3_r;

        let write_opt (fd : Core_unix.File_descr.t) (s : string option) =
          let oc = Core_unix.out_channel_of_descr fd in
          Option.iter s ~f:(fun s ->
              Out_channel.output_string oc s;
              Out_channel.flush oc);
          Out_channel.close oc
        in
        write_opt stdin_w input;
        write_opt in1_w input1;
        write_opt in2_w input2;
        write_opt in3_w input3;

        let ic_out = Core_unix.in_channel_of_descr stdout_r in
        let ic_err = Core_unix.in_channel_of_descr stderr_r in
        let out = In_channel.input_all ic_out in
        let err = In_channel.input_all ic_err in
        In_channel.close ic_out;
        In_channel.close ic_err;

        (match Core_unix.waitpid pid with
        | Ok () -> Ok { stdout = out; stderr = err }
        | Error _ -> Error { stdout = out; stderr = err })

  let run_concat ?input ?input1 ?input2 ?input3 ?env ~prog ~args () :
      String.t ResultM(String).t =
    match run ?input ?input1 ?input2 ?input3 ?env ~prog ~args () with
    | Ok { stdout; stderr } -> Ok (stdout ^ stderr)
    | Error { stdout; stderr } -> Error (stdout ^ stderr)
end
