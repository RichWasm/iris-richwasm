From stdpp Require Import base.

Require Import list_util.
Require Export typing.
Require Import annotated_term.

Inductive HasTypePreInstr :
  StoreTyping -> Module_Ctx -> Function_Ctx ->
  Local_Ctx -> PreInstruction -> ArrowType -> Local_Ctx -> Prop :=
| PTStructGet : forall S C F L n taus szs tau l cap,
    M.is_empty (LinTyp S) = true ->
    let psi := StructType (combine taus szs) in
    length taus = length szs ->
    nth_error taus n = Some tau ->
    TypQualLeq F tau Unrestricted = Some true ->
    LocalCtxValid F L ->
    TypeValid F (RefT cap l psi) ->
    TypeValid F tau ->
    QualValid (qual F) (get_hd (linear F)) ->
    HasTypePreInstr S C F L (StructGet n)
      (Arrow [RefT cap l psi]
         [RefT cap l psi; tau])
      L
with HasTypeInstr :
  StoreTyping -> Module_Ctx -> Function_Ctx ->
  Local_Ctx -> Instruction -> ArrowType -> Local_Ctx -> Prop :=
| TAnnot: forall S C F L pe τ L',
    HasTypePreInstr S C F L pe τ L' ->
    HasTypeInstr S C F L (Instr pe τ) τ L'
with HasTypeInstrs :
  StoreTyping -> Module_Ctx -> Function_Ctx ->
  Local_Ctx -> list Instruction -> ArrowType -> Local_Ctx -> Prop :=
| TSOne: forall S C F L e τ L',
    HasTypeInstr S C F L e τ L' ->
    HasTypeInstrs S C F L [e] τ L'.
