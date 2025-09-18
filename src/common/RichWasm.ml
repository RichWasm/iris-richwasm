open! Base

module PrimativeRep = struct
  type t = [%import: Richwasm_extract.RwSyntax.Core.primitive_rep]
end
