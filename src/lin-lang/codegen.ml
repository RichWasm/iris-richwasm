open! Base

module CGErr = struct
  type t
end

module CodeGen = struct
  open Cc
  module A = Closed

  let compile : A.modul -> unit = function
    | _ -> ()
end
