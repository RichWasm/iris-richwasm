open Brr
module P = Richwasm_web_protocol.Protocol
module W = Richwasm_workspace
module Worker = Brr_webworkers.Worker
module CM = Codemirror

let run_timeout_ms = 5000
let compile_delay_ms = 250

let languages ~constructors : W.view -> CM.Language.t =
  let rich_wasm = CM.Language.rich_wasm constructors in
  function
  | Source MiniML -> CM.Language.mini_ml ()
  | Source LinLang -> CM.Language.lin_lang ()
  | Source RichWasm -> rich_wasm
  | Source Wasm | Wat -> CM.Language.wast ()
  | RichWasm_pretty -> CM.Language.pretty ()

type built = {
  wasm : Jv.t;
  start_type : string option;
}

type compiled = {
  stages : W.stage list;
  result : (built, string * string) result;
}

type file = {
  path : string;
  doc : CM.Doc.t;
  mutable latest_request : int;
  mutable compiled : compiled option;
  mutable compile_timer : G.timer_id option;
}

let compiled ~stages ~(outcome : P.Reply.outcome) wasm =
  let result =
    match (outcome, wasm) with
    | Built { start_type }, Some wasm -> Ok { wasm; start_type }
    | Built _, None -> Error ("compile", "the reply carries no Wasm")
    | Failed { stage; message }, _ -> Error (stage, message)
  in
  { stages; result }

let on_message target f =
  ignore
    (Ev.listen Brr_io.Message.Ev.message
       (fun ev -> f (Brr_io.Message.Ev.data (Ev.as_type ev)))
       target)

let on target ev f = ignore (Ev.listen ev (fun _ -> f ()) (El.as_target target))

let classed (cons : El.cons) cls children =
  cons ~at:[ At.class' (Jstr.v cls) ] children

let set_text el text = El.set_children el [ El.txt' text ]

let set_rows el rows =
  El.set_children el
    (List.concat_map
       (fun (label, value) ->
         [ classed El.span "label" [ El.txt' label ]; El.pre [ El.txt' value ] ])
       rows)

let run ~modules ~links k =
  let worker = Worker.create (Jstr.v "run_worker.js") in
  let finish result =
    Worker.terminate worker;
    k result
  in
  let timer =
    G.set_timeout ~ms:run_timeout_ms (fun () ->
        finish (Error (Printf.sprintf "timed out after %d ms" run_timeout_ms)))
  in
  on_message (Worker.as_target worker) (fun data ->
      G.stop_timer timer;
      finish
        (match Jv.find data "error" with
        | Some error -> Error (Jv.to_string error)
        | None ->
            Ok
              ( Jv.to_bool (Jv.get data "typed"),
                Jv.to_string (Jv.get data "output") )));
  let spec =
    W.run_spec
      ~modules:(List.map (fun (name, _, t) -> (name, t)) modules)
      ~links
  in
  Worker.post worker
    (Jv.obj
       [|
         ("spec", Jv.of_string spec);
         ("wasms", Jv.of_list (fun (_, wasm, _) -> wasm) modules);
       |])

let linkable files =
  let ( let* ) = Result.bind in
  let* modules =
    List.fold_right
      (fun f acc ->
        let* acc = acc in
        match (W.lang_of_path f.path, f.compiled) with
        | None, _ -> Ok acc
        | Some _, Some { result = Ok { wasm; start_type }; _ } ->
            Ok ((W.module_name f.path, wasm, start_type) :: acc)
        | Some _, Some { result = Error _; _ } ->
            Error (f.path ^ " does not compile")
        | Some _, None -> Error (f.path ^ " is still compiling"))
      files (Ok [])
  in
  let* links =
    match List.find_opt (fun f -> f.path = W.links_file) files with
    | None -> Ok []
    | Some f -> W.parse_links (CM.Doc.value f.doc)
  in
  Ok (modules, links)

let start
    compiler
    ~(language_of : W.view -> CM.Language.t)
    ~(examples : P.Reply.example list) =
  let files = ref [] and current = ref None and selected_stage = ref "Wasm" in
  let next_id = ref 0 in
  let file_list = classed El.div "files" [] in
  let new_file =
    El.input
      ~at:[ At.class' (Jstr.v "new-file"); At.placeholder (Jstr.v "new file…") ]
      ()
  in
  let source_host = classed El.div "editor" [] in
  let stage_host = classed El.div "editor" [] in
  let tabs = classed El.nav "tabs" [] in
  let output = classed El.div "output" [] in
  let status = classed El.span "status" [] in
  let run_button = El.button [ El.txt' "Run" ] in
  let example_select =
    El.select
      (List.mapi
         (fun i (e : P.Reply.example) ->
           El.option ~at:[ At.value (Jstr.of_int i) ] [ El.txt' e.name ])
         examples)
  in
  El.set_children (Document.body G.document)
    [
      El.header
        [ El.h1 [ El.txt' "RichWasm" ]; example_select; run_button; status ];
      El.v (Jstr.v "main")
        [
          classed El.aside "workspace" [ file_list; new_file ];
          classed El.section "source" [ source_host ];
          classed El.section "stages"
            [
              tabs;
              stage_host;
              classed El.nav "tabs"
                [ classed El.span "title" [ El.txt' "Output" ] ];
              output;
            ];
        ];
    ];
  let source_view = CM.View.create source_host in
  let stage_view = CM.View.create stage_host in
  let language_of_path path =
    match W.lang_of_path path with
    | Some lang -> language_of (Source lang)
    | None -> CM.Language.plain ()
  in
  let expected () =
    List.find_opt (fun f -> f.path = W.expected_file) !files
    |> Option.map (fun f -> String.trim (CM.Doc.value f.doc))
  in
  let is_current f =
    match !current with
    | Some g -> g == f
    | None -> false
  in
  let rec render_files () =
    El.set_children file_list
      (List.map
         (fun f ->
           let mark =
             match (W.lang_of_path f.path, f.compiled) with
             | None, _ -> ""
             | Some _, Some { result = Ok _; _ } -> "✓"
             | Some _, Some { result = Error _; _ } -> "✗"
             | Some _, None -> "…"
           in
           let open_button =
             El.button
               [ El.txt' f.path; classed El.span "mark" [ El.txt' mark ] ]
           in
           let delete_button = classed El.button "delete" [ El.txt' "×" ] in
           El.set_class (Jstr.v "active") (is_current f) open_button;
           on open_button Ev.click (fun () -> open_file f);
           on delete_button Ev.click (fun () -> delete f);
           classed El.div "file" [ open_button; delete_button ])
         !files)
  and render_stages () =
    let stages =
      match !current with
      | Some { compiled = Some c; _ } -> c.stages
      | _ -> []
    in
    let shown =
      match
        List.find_opt (fun (s : W.stage) -> s.title = !selected_stage) stages
      with
      | Some s -> Some s
      | None -> List.fold_left (fun _ s -> Some s) None stages
    in
    El.set_children tabs
      (List.map
         (fun (s : W.stage) ->
           let b = El.button [ El.txt' s.title ] in
           El.set_class (Jstr.v "active") (Some s = shown) b;
           on b Ev.click (fun () ->
               selected_stage := s.title;
               render_stages ());
           b)
         stages);
    let text, view =
      match shown with
      | Some s -> (s.text, s.view)
      | None -> ("", W.Wat)
    in
    CM.View.show stage_view
      (CM.Doc.create ~read_only:true ~language:(language_of view) text)
  and render_status () =
    match !current with
    | Some { compiled = Some { result = Error (stage, message); _ }; _ } ->
        set_text status (stage ^ " failed");
        set_rows output [ ("error", message) ]
    | _ ->
        set_text status
          (match linkable !files with
          | Ok _ -> "ready to run"
          | Error why -> why);
        set_rows output
          (Option.fold ~none:[]
             ~some:(fun e -> [ ("expected", e) ])
             (expected ()))
  and open_file f =
    current := Some f;
    CM.View.show source_view f.doc;
    render_files ();
    render_stages ();
    render_status ()
  and delete f =
    Option.iter G.stop_timer f.compile_timer;
    files := List.filter (fun g -> g != f) !files;
    match (!current, !files) with
    | Some g, h :: _ when g == f -> open_file h
    | _ ->
        render_files ();
        render_status ()
  in
  let compile f =
    (match W.lang_of_path f.path with
    | None -> ()
    | Some lang ->
        incr next_id;
        f.latest_request <- !next_id;
        f.compiled <- None;
        Worker.post compiler
          (P.encode P.Request.sexp_of_t
             {
               body =
                 Compile
                   {
                     id = !next_id;
                     path = f.path;
                     lang;
                     source = CM.Doc.value f.doc;
                   };
               wasm = None;
             }));
    render_files ();
    render_status ()
  in
  let add path text =
    let doc = CM.Doc.create ~language:(language_of_path path) text in
    let f =
      { path; doc; latest_request = 0; compiled = None; compile_timer = None }
    in
    files := !files @ [ f ];
    compile f;
    f
  in
  let load (e : P.Reply.example) =
    files := [];
    let added = List.map (fun (path, text) -> add path text) e.files in
    match List.find_opt (fun f -> W.module_name f.path = "main") added with
    | Some f -> open_file f
    | None -> Option.iter open_file (List.nth_opt added 0)
  in
  CM.View.on_change source_view (fun doc ->
      match List.find_opt (fun f -> CM.Doc.equal f.doc doc) !files with
      | None -> ()
      | Some f ->
          Option.iter G.stop_timer f.compile_timer;
          f.compile_timer <-
            Some (G.set_timeout ~ms:compile_delay_ms (fun () -> compile f)));
  ignore
    (Ev.listen Ev.keydown
       (fun ev ->
         if Jstr.equal (Ev.Keyboard.key (Ev.as_type ev)) (Jstr.v "Enter") then
           let path =
             String.trim (Jstr.to_string (El.prop El.Prop.value new_file))
           in
           if path <> "" && not (List.exists (fun f -> f.path = path) !files)
           then (
             El.set_prop El.Prop.value Jstr.empty new_file;
             open_file (add path "")))
       (El.as_target new_file));
  on example_select Ev.change (fun () ->
      Option.iter
        (fun i -> load (List.nth examples i))
        (int_of_string_opt
           (Jstr.to_string (El.prop El.Prop.value example_select))));
  on run_button Ev.click (fun () ->
      match linkable !files with
      | Error why -> set_rows output [ ("cannot run", why) ]
      | Ok (modules, links) ->
          set_rows output [ ("result", "running…") ];
          run ~modules ~links (fun result ->
              let shown, matches =
                match result with
                | Ok (typed, text) ->
                    ( ((if typed then "result" else "raw result"), text),
                      ( = ) text )
                | Error why -> (("error", why), Fun.const false)
              in
              set_rows output
                (shown
                :: Option.fold ~none:[]
                     ~some:(fun e ->
                       [ ("expected", e ^ if matches e then "  ✓" else "  ✗") ])
                     (expected ()))));
  Option.iter load (List.nth_opt examples 0);
  fun ~id ~path compiled ->
    match
      List.find_opt (fun f -> f.path = path && f.latest_request = id) !files
    with
    | None -> ()
    | Some f ->
        f.compiled <- Some compiled;
        render_files ();
        if is_current f then render_stages ();
        render_status ()

let () =
  let compiler = Worker.create (Jstr.v "compiler_worker.js") in
  let on_compiled = ref (fun ~id:_ ~path:_ _ -> ()) in
  on_message (Worker.as_target compiler) (fun data ->
      let ({ body; wasm } : P.Reply.t P.message) =
        P.decode P.Reply.t_of_sexp data
      in
      match body with
      | Ready { constructors; examples } ->
          on_compiled :=
            start compiler ~language_of:(languages ~constructors) ~examples
      | Compiled { id; path; stages; outcome } ->
          !on_compiled ~id ~path (compiled ~stages ~outcome wasm))
