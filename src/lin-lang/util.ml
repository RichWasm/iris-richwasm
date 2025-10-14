open! Base

let flatten (lst : 'a list list) : 'a list =
  let rec go acc = function
    | [] -> List.rev acc
    | m :: ms -> go (List.rev_append m acc) ms
  in
  go [] lst

include Richwasm_common.Monads
