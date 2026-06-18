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

  (** Spawn child with:
      - stdin <- [input] (fd 0)
      - stdout -> captured (fd 1)
      - stderr -> captured (fd 2)
      - [inputs] -> fd 3, 4, ... in order *)
  let run ?input ?(inputs = []) ?(env = `Extend []) ~prog ~args () :
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
    let extra = List.map inputs ~f:(fun payload -> (payload, mk_pipe ())) in

    match Core_unix.fork () with
    | `In_the_child ->
        let dup2_keep ~src ~dst =
          Core_unix.dup2 ~src ~dst ~close_on_exec:false ()
        in
        Core_unix.close stdin_w;
        Core_unix.close stdout_r;
        Core_unix.close stderr_r;
        List.iter extra ~f:(fun (_, (_, w)) -> Core_unix.close w);

        dup2_keep ~src:stdin_r ~dst:Core_unix.stdin;
        dup2_keep ~src:stdout_w ~dst:Core_unix.stdout;
        dup2_keep ~src:stderr_w ~dst:Core_unix.stderr;
        List.iteri extra ~f:(fun i (_, (r, _)) ->
            dup2_keep ~src:r ~dst:(Core_unix.File_descr.of_int (3 + i)));

        Core_unix.close stdin_r;
        Core_unix.close stdout_w;
        Core_unix.close stderr_w;
        List.iter extra ~f:(fun (_, (r, _)) -> Core_unix.close r);

        Core_unix.exec ~prog ~argv:(prog :: args) ~env () |> Core.never_returns
    | `In_the_parent pid ->
        Core_unix.close stdin_r;
        Core_unix.close stdout_w;
        Core_unix.close stderr_w;
        List.iter extra ~f:(fun (_, (r, _)) -> Core_unix.close r);

        let write_close (fd : Core_unix.File_descr.t) (s : string option) =
          let oc = Core_unix.out_channel_of_descr fd in
          Option.iter s ~f:(fun s ->
              Out_channel.output_string oc s;
              Out_channel.flush oc);
          Out_channel.close oc
        in
        write_close stdin_w input;
        List.iter extra ~f:(fun (payload, (_, w)) ->
            write_close w (Some payload));

        let ic_out = Core_unix.in_channel_of_descr stdout_r in
        let ic_err = Core_unix.in_channel_of_descr stderr_r in
        let out = In_channel.input_all ic_out in
        let err = In_channel.input_all ic_err in
        In_channel.close ic_out;
        In_channel.close ic_err;

        (match Core_unix.waitpid pid with
        | Ok () -> Ok { stdout = out; stderr = err }
        | Error _ -> Error { stdout = out; stderr = err })

  let run_concat ?input ?inputs ?env ~prog ~args () : String.t ResultM(String).t
      =
    match run ?input ?inputs ?env ~prog ~args () with
    | Ok { stdout; stderr } -> Ok (stdout ^ stderr)
    | Error { stdout; stderr } -> Error (stdout ^ stderr)
end
