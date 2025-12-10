open! Base
open! Stdlib.Format

module Outputter = struct
  module type Config = sig
    val margin : int
    val max_indent : int
  end

  module DefaultConfig : Config = struct
    let margin = 80
    let max_indent = 80
  end

  module type Core = sig
    include Config

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
    val output_unsafe : text -> unit
    val output_syntax_unsafe : syntax -> unit
  end

  module Make (M : Core) :
    S with type syntax = M.syntax and type text = M.text and type res = M.res =
  struct
    include M

    module Internal = struct
      let mk_ff () =
        let ff = formatter_of_out_channel Stdlib.stdout in
        pp_set_margin ff M.margin;
        pp_set_max_indent ff M.max_indent;
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

    let mk_output_unsafe (pipeline : 'a -> res) =
      let ff = Internal.mk_ff () in
      fun (x : 'a) -> x |> pipeline |> fprintf ff "@.%a@." M.pp

    let output_unsafe = mk_output_unsafe M.string_pipeline
    let output_syntax_unsafe = mk_output_unsafe M.syntax_pipeline
  end
end

module MultiOutputter = struct
  module DefaultConfig = Outputter.DefaultConfig

  module type Core = sig
    include Outputter.Core

    val pp_raw : formatter -> res -> unit
  end

  module type S = sig
    include Core

    val output : text -> unit
    val output_syntax : syntax -> unit
    val output_examples : unit -> unit
    val output_unsafe : text -> unit
    val output_syntax_unsafe : syntax -> unit
    val run : text -> unit
    val run_syntax : text -> unit
    val next : unit -> unit
  end

  module Make (M : Core) = struct
    include Outputter.Make (M)

    let pp_raw = M.pp_raw
    let suspended = ref (fun () -> ())

    let mk_run (pipeline : 'a -> res) =
      let ff = Internal.mk_ff () in
      fun (x : 'a) ->
        try
          let r = x |> pipeline in
          fprintf ff "@.%a@." pp r;
          suspended := fun () -> fprintf ff "@.%a@." pp_raw r
        with Failure msg ->
          fprintf ff "@.FAILURE %s@." msg;
          suspended := fun () -> fprintf ff "@.Failure ^^^@."

    let run = mk_run string_pipeline
    let run_syntax = mk_run syntax_pipeline

    let next () =
      !suspended ();
      suspended := fun () -> ()
  end
end
