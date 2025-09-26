open Base
open RichWasm
open Syntax

let translate_num_type t : PrimitiveRep.t * NumType.t =
  match t with
  | Int I32 -> I32R, IntT I32T
  | Int I64 -> I64R, IntT I64T
  | Float F32 -> F32R, FloatT F32T
  | Float F64 -> F64R, FloatT F64T

let translate_type t : Type.t =
  match t with
  | Var n -> VarT (Z.of_int n)
  | Num t' ->
      let p, t'' = translate_num_type t' in
      NumT (VALTYPE (PrimR p, ImCopy, ImDrop), t'')
  | _ -> failwith "TODO"

let infer ts1 ts2 e =
  match e with
  | Nop -> Instruction.INop (InstrT ([], []))
  | Unreachable -> Instruction.IUnreachable (InstrT (ts1, ts2))
  | Copy ->
      let t = List.hd_exn ts1 in
      Instruction.ICopy (InstrT ([t], [t; t]))
  | Drop -> Instruction.IDrop (InstrT (List.take ts1 1, []))
  | Num _ -> failwith "TODO"
  | NumConst (t, n) ->
      let t' = translate_type (Num t) in
      Instruction.INumConst (InstrT ([], [t']), Z.of_int n)
  | _ -> failwith "TODO"
