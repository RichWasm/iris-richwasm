From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt.

Set Warnings "-extraction-default-directory".

Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Optimize.

From RichWasm.syntax Require rw.

Extraction "RwSyntax.ml" rw.Core.instruction.
