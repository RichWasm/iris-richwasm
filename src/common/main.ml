open! Base

let elaborate = Elaborate.elab_module

let compile = Richwasm_extract.Module0.compile_module

let serialize = Richwasm_extract.Binary_format_printer.binary_of_module
