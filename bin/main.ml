open! Core
open! Core_unix

let lin_lang =
  Command.basic ~summary:""
    (let%map_open.Command filename = anon ("file_name" %: string)
     and output = anon ("output" %: string) in
     fun () ->
       print_endline filename;
       print_endline output)

let mini_ml =
  Command.basic ~summary:""
    (let%map_open.Command arg = anon ("todo" %: string) in
     fun () -> print_endline arg)

(* TODO: how do we want to handle linking? *)
let run =
  Command.basic ~summary:"Run a compiled RichWasm module"
    (let%map_open.Command wasm = anon ("wasm_file" %: string) in
     fun () -> print_endline wasm)

let command =
  Command.group ~summary:"iris-richwasm"
    [ ("lin-lang", lin_lang); ("mini-ml", mini_ml); ("run", run) ]

let () = Command_unix.run command
