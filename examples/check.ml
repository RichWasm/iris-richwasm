open! Core
module W = Richwasm_workspace

module Dir = Richwasm_support.Run_rw.DirRichWasm (struct
  let rw_runtime_path = Sys.getenv_exn "RW_RUNTIME_WASM_PATH"
  let host_runtime_path = Sys.getenv_exn "HOST_LINK_PATH"
end)

let () =
  let failures =
    Stdlib.Sys.readdir "."
    |> Array.to_list
    |> List.sort ~compare:String.compare
    |> List.filter ~f:(fun dir ->
        Stdlib.Sys.file_exists (Filename.concat dir W.expected_file))
    |> List.filter_map ~f:(fun dir ->
        let expected =
          String.strip
            (In_channel.read_all (Filename.concat dir W.expected_file))
        in
        match Dir.run_dir dir with
        | Ok output when String.equal (String.strip output) expected -> None
        | Ok output ->
            Some (sprintf "%s: printed %s, expected %s" dir output expected)
        | Error err -> Some (sprintf "%s: %s" dir err))
  in
  List.iter failures ~f:print_endline;
  if not (List.is_empty failures) then exit 1
