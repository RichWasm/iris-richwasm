let sorted_entries dir = Sys.readdir dir |> Array.to_list |> List.sort compare

let () =
  let root = Sys.argv.(1) in
  let examples =
    sorted_entries root
    |> List.filter (fun d ->
        d <> "embed" && Sys.is_directory (Filename.concat root d))
  in
  print_string "let all = [\n";
  List.iter
    (fun name ->
      let dir = Filename.concat root name in
      Printf.printf "  (%S, [\n" name;
      List.iter
        (fun file ->
          let contents =
            In_channel.with_open_bin (Filename.concat dir file)
              In_channel.input_all
          in
          Printf.printf "    (%S, %S);\n" file contents)
        (sorted_entries dir
        |> List.filter (fun f ->
            f <> "dune" && not (Sys.is_directory (Filename.concat dir f))));
      print_string "  ]);\n")
    examples;
  print_string "]\n"
