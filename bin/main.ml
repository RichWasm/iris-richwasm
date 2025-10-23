open! Core
open! Core_unix

let lin_lang =
  Command.basic ~summary:""
    (let%map_open.Command filename = anon ("file_name" %: string) in
     fun () -> print_endline filename)

let command = Command.group ~summary:"iris-richwasm" [ ("lin-lang", lin_lang) ]
let () = Command_unix.run command
