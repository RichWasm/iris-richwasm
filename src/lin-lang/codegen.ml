open! Base
open Richwasm_common

module CGErr = struct
  type t
end

module Compile = struct
  module A = Cc.IR
  module B = RichWasm

  let compile_import ({ typ; name } : A.Import.t) = ()

  let compile ({ imports; toplevels; main } : A.Module.t) : B.Module.t =
    let m_imports = [] in
    let m_exports = [] in
    let m_globals = [] in
    let m_funcs = [] in
    let m_table = [] in
    let m_start = None in
    { m_imports; m_exports; m_globals; m_funcs; m_table; m_start }
end
