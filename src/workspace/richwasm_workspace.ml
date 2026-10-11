open Sexplib0.Sexp_conv

type lang =
  | MiniML
  | LinLang
  | RichWasm
  | Wasm
[@@deriving sexp]

type view =
  | Source of lang
  | RichWasm_pretty
  | Wat
[@@deriving sexp]

type stage = {
  title : string;
  view : view;
  text : string;
}
[@@deriving sexp]

let lang_of_path path =
  match Filename.extension path with
  | ".mml" -> Some MiniML
  | ".ll" -> Some LinLang
  | ".rw" -> Some RichWasm
  | ".wat" -> Some Wasm
  | _ -> None

let module_name path = Filename.remove_extension path

(** Import [index] of [importer] is [provider]'s export [export]. *)
type link = {
  importer : string;
  index : int;
  provider : string;
  export : string;
}
[@@deriving sexp]

let links_file = "links.sexp"
let expected_file = "expected"

let parse_links text =
  match Parsexp.Single.parse_string text with
  | Error e -> Error (links_file ^ ": " ^ Parsexp.Parse_error.message e)
  | Ok sexp ->
      (match list_of_sexp link_of_sexp sexp with
      | links -> Ok links
      | exception e -> Error (links_file ^ ": " ^ Printexc.to_string e))

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c when Char.code c < 0x20 ->
          Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let json_object fields =
  "{"
  ^ String.concat "," (List.map (fun (k, v) -> json_string k ^ ":" ^ v) fields)
  ^ "}"

let json_array xs = "[" ^ String.concat "," xs ^ "]"

(** The JSON [RunSpec] of [link.ts]. *)
let run_spec ~(modules : (string * string option) list) ~(links : link list) =
  let module_json (name, start_type) =
    json_object
      (("name", json_string name)
      :: Option.fold ~none:[]
           ~some:(fun t -> [ ("startType", json_string t) ])
           start_type)
  in
  let link_json l =
    json_object
      [
        ("importer", json_string l.importer);
        ("index", string_of_int l.index);
        ("provider", json_string l.provider);
        ("export", json_string l.export);
      ]
  in
  json_object
    [
      ("modules", json_array (List.map module_json modules));
      ("links", json_array (List.map link_json links));
    ]
