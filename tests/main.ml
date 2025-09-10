open Richwasm_lin_lang.Syntax
open Format

let () =
  let examples : (string * Module.t) list =
    Lin_lang.Examples.
      [
        ("add_one_program", add_one_program);
        ("swap_pair_program", swap_pair_program);
        ("compose_program", compose_program);
        ("reference_example", reference_example);
        ("factorial_program", factorial_program);
        ("module_with_imports", module_with_imports);
        ("complex_example", complex_example);
        ("closure_example", closure_example);
      ]
  in
  let fmt = Format.std_formatter in
  Format.pp_set_margin fmt 120;
  Format.pp_set_max_indent fmt 80;
  List.iter (fun (n, m) -> printf "%s\n----------\n%a\n\n" n Module.pp m) examples
