open Sexplib0.Sexp_conv
module W = Richwasm_workspace

module Request = struct
  type t =
    | Compile of {
        id : int;
        path : string;
        lang : W.lang;
        source : string;
      }
  [@@deriving sexp]
end

module Reply = struct
  type example = {
    name : string;
    files : (string * string) list;
  }
  [@@deriving sexp]

  type constructors = {
    instructions : string list;
    types : string list;
  }
  [@@deriving sexp]

  type outcome =
    | Built of { start_type : string option }
    | Failed of {
        stage : string;
        message : string;
      }
  [@@deriving sexp]

  type t =
    | Ready of {
        constructors : constructors;
        examples : example list;
      }
    | Compiled of {
        id : int;
        path : string;
        stages : W.stage list;
        outcome : outcome;
      }
  [@@deriving sexp]
end

type 'a message = {
  body : 'a;
  wasm : Jv.t option;
}

let encode sexp_of { body; wasm } =
  Jv.obj
    [|
      ("sexp", Jv.of_string (Sexplib0.Sexp.to_string (sexp_of body)));
      ("wasm", Option.value wasm ~default:Jv.undefined);
    |]

let decode of_sexp jv =
  let body =
    of_sexp (Parsexp.Single.parse_string_exn (Jv.to_string (Jv.get jv "sexp")))
  in
  let wasm = Jv.get jv "wasm" in
  { body; wasm = (if Jv.is_none wasm then None else Some wasm) }
