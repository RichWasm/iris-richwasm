let wabt () = Jv.get Jv.global "wabt"
let features = Jv.obj [| ("multi_memory", Jv.true') |]

let with_module m f =
  Fun.protect
    ~finally:(fun () -> ignore (Jv.call m "destroy" [||]))
    (fun () -> f m)

let catch f =
  match f () with
  | v -> Ok v
  | exception Jv.Error e -> Error (Jstr.to_string (Jv.Error.message e))

let wat2wasm (wat : string) : (Jv.t, string) result =
  catch @@ fun () ->
  with_module
    (Jv.call (wabt ()) "parseWat"
       [| Jv.of_string "module.wat"; Jv.of_string wat; features |])
    (fun m ->
      ignore (Jv.call m "resolveNames" [||]);
      ignore (Jv.call m "validate" [| features |]);
      Jv.get (Jv.call m "toBinary" [| Jv.obj [||] |]) "buffer")

let wasm2wat (wasm : Jv.t) : (string, string) result =
  catch @@ fun () ->
  let opts =
    Jv.obj [| ("readDebugNames", Jv.true'); ("multi_memory", Jv.true') |]
  in
  with_module
    (Jv.call (wabt ()) "readWasm" [| wasm; opts |])
    (fun m ->
      ignore (Jv.call m "generateNames" [||]);
      ignore (Jv.call m "applyNames" [||]);
      Jv.to_string
        (Jv.call m "toText"
           [|
             Jv.obj [| ("foldExprs", Jv.true'); ("inlineExport", Jv.true') |];
           |]))
