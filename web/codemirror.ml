open Brr

let api () = Jv.get Jv.global "richwasmEditor"

module Language = struct
  type t = Jv.t

  let get name () = Jv.get (api ()) name
  let mini_ml = get "miniml"
  let lin_lang = get "linlang"
  let pretty = get "pretty"
  let wast = get "wast"
  let plain = get "plain"

  let rich_wasm
      ({ instructions; types } :
        Richwasm_web_protocol.Protocol.Reply.constructors) =
    let words = Jv.of_list Jv.of_string in
    Jv.call (api ()) "richWasm"
      [|
        Jv.obj
          [| ("instructions", words instructions); ("types", words types) |];
      |]
end

module Doc = struct
  type t = Jv.t

  let create ?(read_only = false) ~(language : Language.t) text =
    Jv.call (api ()) "makeDoc"
      [| Jv.of_string text; language; Jv.of_bool read_only |]

  let value t = Jv.to_string (Jv.call t "value" [||])
  let equal = Jv.strict_equal
end

module View = struct
  type t = Jv.t

  let create host = Jv.call (api ()) "createView" [| El.to_jv host |]
  let show t (doc : Doc.t) = ignore (Jv.call t "open" [| doc |])

  let on_change t (f : Doc.t -> unit) =
    ignore (Jv.call t "onChange" [| Jv.callback ~arity:1 f |])
end
