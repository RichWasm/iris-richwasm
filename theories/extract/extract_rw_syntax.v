From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNativeString.

Set Warnings "-extraction-default-directory".

Extract Inductive nat => "Z.t"
  [ "Z.zero" "Z.succ" ]
  "(fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))".

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Optimize.

From RichWasm.syntax Require rw modules.

Extraction "RwSyntax.ml" rw.Core.instruction modules.module.
