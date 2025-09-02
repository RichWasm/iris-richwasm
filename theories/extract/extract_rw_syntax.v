From Coq Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Extraction Language OCaml.
Set Extraction AutoInline.
Set Extraction Optimize.

From RichWasm.syntax Require rw.

Extraction "RwSyntax.ml" rw.Core.instruction.
