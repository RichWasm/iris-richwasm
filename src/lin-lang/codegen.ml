module CGErr = struct
  type t
end

module CodeGen = struct
  open Cc
  module A = Declosure

  let compile : A.modul -> unit = function
    | _ -> ()
end
