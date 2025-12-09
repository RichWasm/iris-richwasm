open! Base
module Big_int_Z' = Annotated_syntax.Big_int_Z'

module Primitive = struct
  type t = [%import: Richwasm_extract.Syntax.primitive]
  [@@deriving eq, ord, sexp]
end

module FunctionEnv = struct
  type t =
    [%import:
      (Richwasm_extract.Prelude.function_env
      [@with
        kind := Annotated_syntax.Kind.t;
        Core.kind := Annotated_syntax.Kind.t;
        Richwasm_extract.Rw.Core.kind := Annotated_syntax.Kind.t;
        coq_type := Annotated_syntax.Type.t;
        Core.coq_type := Annotated_syntax.Type.t;
        Richwasm_extract.Rw.Core.coq_type := Annotated_syntax.Type.t;
        primitive := Primitive.t;
        Richwasm_extract.Syntax.primitive := Primitive.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]
end

module CompilerError = struct
  type t =
    [%import:
      (Richwasm_extract.Prelude.error
      [@with
        function_env := FunctionEnv.t;
        Richwasm_extract.Prelude.function_env := FunctionEnv.t;
        Big_int_Z.big_int := Big_int_Z'.big_int])]
  [@@deriving eq, ord, sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end
