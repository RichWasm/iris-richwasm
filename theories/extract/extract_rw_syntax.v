From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNativeString.

Set Warnings "-extraction-default-directory".

Extract Inductive nat => "Z.t"
  [ "Z.zero" "Z.succ" ]
  "(fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))".

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Optimize.

From RichWasm.syntax Require rw module.

Extraction "RwSyntax.ml"
  rw.Core.instruction
  rw.Core.subst_instruction
  rw.Core.subst_instruction_type
  rw.Core.subst_function_type
  rw.Core.subst_type
  rw.Core.ren_function_type
  rw.Core.ren_type
  rw.Core.subst_kind
  rw.Core.ren_kind
  rw.Core.subst_sizity
  rw.Core.ren_sizity
  rw.Core.subst_memory
  rw.Core.ren_memory
  rw.Core.subst_size
  rw.Core.ren_size
  rw.Core.subst_representation
  rw.Core.ren_representation
  module.module.
