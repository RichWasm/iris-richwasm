From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZInt ExtrOcamlZBigInt ExtrOcamlNatBigInt ExtrOcamlNativeString.
Set Warnings "-extraction-default-directory".

Extraction Language OCaml.
(* Set Extraction AutoInline. *)
(* Set Extraction Optimize. *)

(* HACK: The following are overridding ExtrOcamlNativeString because it doesn't properly qualify 
  ocaml's Stdlib functions, which can get shadowed by Roqc's Stdlib. *)
Extract Inlined Constant String.concat => "Stdlib.String.concat".
Extract Inlined Constant String.prefix =>
  "(fun s1 s2 -> let l1 = Stdlib.String.length s1 and l2 = Stdlib.String.length s2 in l1 <= l2 && Stdlib.String.sub s2 0 l1 = s1)".
Extract Inlined Constant String.string_of_list_ascii =>
  "(fun l -> let a = Stdlib.Array.of_list l in Stdlib.String.init (Stdlib.Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant String.list_ascii_of_string =>
  "(fun s -> Stdlib.List.init (Stdlib.String.length s) (fun i -> Stdlib.String.get s i))".
Extract Inlined Constant String.string_of_list_byte =>
  "(fun l -> let a = Stdlib.Array.of_list l in Stdlib.String.init (Stdlib.Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant String.list_byte_of_string =>
  "(fun s -> Stdlib.List.init (Stdlib.String.length s) (fun i -> Stdlib.String.get s i))".


From RichWasm.syntax Require rw module.
Module rw_module_syntax := module.

From RichWasm.compiler Require module.
Module rw_module_compiler := module.

From Wasm Require binary_format_printer.

Separate Extraction
  rw.Core.instruction
  rw.Core.subst_instruction
  rw.Core.subst_instruction_type
  rw.Core.subst_function_type
  rw.Core.subst_type
  rw.Core.ren_function_type
  rw.Core.ren_type
  rw.Core.subst_kind
  rw.Core.ren_kind
  rw.Core.subst_memory
  rw.Core.ren_memory
  rw.Core.subst_size
  rw.Core.ren_size
  rw.Core.subst_representation
  rw.Core.ren_representation
  rw_module_syntax.module
  rw_module_compiler.compile_module
  binary_format_printer.binary_of_module.
