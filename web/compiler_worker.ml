open! Base
open Brr
module P = Richwasm_web_protocol.Protocol

module Build = Richwasm_build.Make (struct
  type wasm = Jv.t

  let wat2wasm = Wabt.wat2wasm
  let wasm2wat = Wabt.wasm2wat
end)

let head_atom : Sexp.t -> string list = function
  | List (Atom head :: _) -> [ head ]
  | _ -> []

let constructors : P.Reply.constructors =
  let open Richwasm_common.Syntax in
  let names = List.concat_map ~f:(List.map ~f:fst) in
  {
    instructions =
      names
        [
          Instruction.Variants.descriptions;
          NumInstruction.Variants.descriptions;
          Int.Unop.Variants.descriptions;
          Int.Binop.Variants.descriptions;
          Int.Testop.Variants.descriptions;
          Int.Relop.Variants.descriptions;
          Float.Unop.Variants.descriptions;
          Float.Binop.Variants.descriptions;
          Float.Relop.Variants.descriptions;
          ConversionOp.Variants.descriptions;
          BlockType.Variants.descriptions;
          LocalFx.Variants.descriptions;
          Consume.Variants.descriptions;
          Module.Export.Desc.Variants.descriptions;
        ];
    types =
      names
        [
          Type.Variants.descriptions;
          Representation.Variants.descriptions;
          AtomicRep.Variants.descriptions;
          Size.Variants.descriptions;
          Kind.Variants.descriptions;
          Quantifier.Variants.descriptions;
          Memory.Variants.descriptions;
          BaseMemory.Variants.descriptions;
          Mutability.Variants.descriptions;
          RefFlag.Variants.descriptions;
          NumType.Variants.descriptions;
          Int.Type.Variants.descriptions;
          Float.Type.Variants.descriptions;
          Sign.Variants.descriptions;
        ]
      @ head_atom (FunctionType.sexp_of_t (FunctionType ([], [], [])));
  }

let examples =
  List.map Richwasm_examples.all ~f:(fun (name, files) ->
      P.Reply.{ name; files })

let post ?wasm body =
  Brr_webworkers.Worker.G.post (P.encode P.Reply.sexp_of_t { body; wasm })

let handle (P.Request.Compile { id; path; lang; source }) =
  let stages, result = Build.compile lang source in
  match result with
  | Ok (wasm, start_type) ->
      post ~wasm (Compiled { id; path; stages; outcome = Built { start_type } })
  | Error (stage, message) ->
      post (Compiled { id; path; stages; outcome = Failed { stage; message } })

let () =
  ignore
    (Ev.listen Brr_io.Message.Ev.message
       (fun ev ->
         handle
           (P.decode P.Request.t_of_sexp
              (Brr_io.Message.Ev.data (Ev.as_type ev)))
             .body)
       G.target);
  post (Ready { constructors; examples })
