From Coq Require Import Numbers.BinNums NArith List.

From RWasm Require Import annotated_term debruijn subst.

(* If you need theorems about this substitution function, you should
   write them in this file following the style of subst.v. *)
Fixpoint subst'_instruction (su : Subst' Kind) (i : Instruction) {struct i} : Instruction :=
  match i with
  | Instr i τ => Instr (subst'_pre_instruction su i) (subst'_arrowtype su τ)
  end
with subst'_pre_instruction (su : Subst' Kind) (i : PreInstruction) {struct i} : PreInstruction :=
  match i with
  | Val v => Val (subst'_value su v)
  | Ne _ => i
  | Unreachable => i
  | Nop => i
  | Drop => i
  | Select => i
  | Block arr leffs insns =>
    Block (subst'_arrowtype su arr)
          (subst'_localeffect su leffs)
          (map (subst'_instruction su) insns)
  | Loop arr insns =>
    Loop (subst'_arrowtype su arr)
         (map (subst'_instruction su) insns)
  | ITE arr leffs insns1 insns2 =>
    ITE (subst'_arrowtype su arr)
        (subst'_localeffect su leffs)
        (map (subst'_instruction su) insns1)
        (map (subst'_instruction su) insns2)
  | Br _ => i
  | Br_if _ => i
  | Br_table _ _ => i
  | Ret => i
  | Get_local n q => Get_local n (subst'_qual su q)
  | Set_local _ => i
  | Tee_local _ => i
  | Get_global _ => i
  | Set_global _ => i
  | CoderefI _ => i
  | Inst insts => Inst (subst'_indices su insts)
  | Call_indirect => i
  | Call n insts => Call n (subst'_indices su insts)
  | RecFold t => RecFold (subst'_typ su t)
  | RecUnfold => i
  | Group n q => Group n (subst'_qual su q)
  | Ungroup => i
  | CapSplit => i
  | CapJoin => i
  | RefDemote => i
  | MemPack l => MemPack (subst'_loc su l)
  | MemUnpack arr leff l_insns =>
    (* l_insns binds a new location *)
    MemUnpack (subst'_arrowtype su arr)
              (subst'_localeffect su leff)
              (map (subst'_instruction (under' SLoc su)) l_insns)
  | StructMalloc ss q => StructMalloc (subst'_sizes su ss) (subst'_qual su q)
  | StructFree => i
  | StructGet _ => i
  | StructSet _ => i
  | StructSwap _ => i
  | VariantMalloc n ts q =>
    VariantMalloc n (subst'_typs su ts) (subst'_qual su q)
  | VariantCase q tausv arr leff insnss =>
    VariantCase (subst'_qual su q)
                (subst'_heaptype su tausv)
                (subst'_arrowtype su arr)
                (subst'_localeffect su leff)
                (map (map (subst'_instruction su)) insnss)
  | ArrayMalloc q => ArrayMalloc (subst'_qual su q)
  | ArrayGet => i
  | ArraySet => i
  | ArrayFree => i
  | ExistPack t ht q =>
    ExistPack (subst'_typ su t)
              (subst'_heaptype su ht)
              (subst'_qual su q)
  | ExistUnpack q ex arr leff α_insns =>
    (* α_insns binds a new type variable *)
    ExistUnpack (subst'_qual su q)
                (subst'_heaptype su ex)
                (subst'_arrowtype su arr)
                (subst'_localeffect su leff)
                (map (subst'_instruction (under' STyp su)) α_insns)
  | RefSplit => i
  | RefJoin => i
  | Qualify q => Qualify (subst'_qual su q)
  | Trap => i
  (* We don't substitute into clo
     because HasTypeClosure requires clo to be closed *)
  | CallAdm clo insts =>
    CallAdm clo
            (subst'_indices su insts)
  | Label n arr insns1 insns2 =>
    Label n (subst'_arrowtype su arr)
          (map (subst'_instruction su) insns1)
          (map (subst'_instruction su) insns2)
  (* We don't substitute into vs and insns
     because HasTypeConf requires vs and insns to be closed *)
  | Local m n vs ss insns =>
    Local m n vs ss insns
  (* We don't substitute into Malloc
     because Malloc is not a surface instruction
     and MallocTyp requires s, hv, q to be closed *)
  | Malloc s hv q =>
    Malloc s hv q
  | Free => i
  end.
