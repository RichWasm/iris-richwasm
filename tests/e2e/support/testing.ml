open! Core
open! Test_support
open! Stdlib.Format

module IDontRespectLibraryInternals = struct
  module Core = Alcotest_engine__Core
  module Pp = Alcotest_engine__Pp

  (* if this ever breaks, its safe to go back to using `fail`.
     it just reports errors twice which is annoying *)
  let custom_fail header msg =
    raise
      (Core.Check_error
         (fun ppf () -> Fmt.pf ppf "%a %s@.%s" Pp.tag `Fail header msg))
end

let custom_fail = IDontRespectLibraryInternals.custom_fail
