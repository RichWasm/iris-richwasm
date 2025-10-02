open! Base
open! Stdlib.Format

let or_fail (p : 'b -> string) : ('a, 'b) Result.t -> 'a = function
  | Ok x -> x
  | Error err -> failwith (p err)

let or_fail_pp (pp : formatter -> 'b -> unit) : ('a, 'b) Result.t -> 'a =
  or_fail (asprintf "%a" pp)

module Outputter = struct
  module type Core = sig
    type syntax
    type text
    type res

    val syntax_pipeline : syntax -> res
    val string_pipeline : text -> res
    val examples : (string * syntax) list
    val pp : formatter -> res -> unit
  end

  module type S = sig
    include Core

    module Internal : sig
      val mk_ff : unit -> formatter
    end

    val output : text -> unit
    val output_syntax : syntax -> unit
    val output_examples : unit -> unit
  end

  module Make (M : Core) :
    S with type syntax = M.syntax and type text = M.text and type res = M.res =
  struct
    include M

    module Internal = struct
      let mk_ff () =
        let ff = formatter_of_out_channel Stdlib.stdout in
        pp_set_margin ff 80;
        pp_set_max_indent ff 80;
        ff
    end

    let mk_output (pipeline : 'a -> res) =
      let ff = Internal.mk_ff () in
      fun (x : 'a) ->
        try x |> pipeline |> fprintf ff "@.%a@." M.pp
        with Failure msg -> fprintf ff "FAILURE %s@." msg

    let output = mk_output M.string_pipeline
    let output_syntax = mk_output M.syntax_pipeline

    let output_examples =
      let ff = Internal.mk_ff () in
      fun () ->
        M.examples
        |> List.iter ~f:(fun (n, s) ->
               try
                 let res = s |> M.syntax_pipeline in
                 fprintf ff "-----------%s-----------@.%a@." n M.pp res
               with Failure msg ->
                 fprintf ff "-----------%s-----------@.FAILURE %s@." n msg)
  end
end

module MultiOutputter = struct
  module type Core = sig
    include Outputter.Core

    val pp_sexp : formatter -> res -> unit
  end

  module type S = sig
    include Core

    val output : text -> unit
    val output_syntax : syntax -> unit
    val output_examples : unit -> unit
    val run : text -> unit
    val next : unit -> unit
  end

  module Make (M : Core) = struct
    include Outputter.Make (M)

    let pp_sexp = M.pp_sexp
    let suspended = ref (fun () -> ())

    let mk_run (pipeline : 'a -> res) =
      let ff = Internal.mk_ff () in
      fun (x : 'a) ->
        try
          let r = x |> pipeline in
          fprintf ff "@.%a@." pp r;
          suspended := fun () -> fprintf ff "@.%a@." pp_sexp r
        with Failure msg ->
          fprintf ff "@.FAILURE %s@." msg;
          suspended := fun () -> fprintf ff "@.Failure ^^^@."

    let run = mk_run string_pipeline

    let next () =
      !suspended ();
      suspended := fun () -> ()
  end
end
