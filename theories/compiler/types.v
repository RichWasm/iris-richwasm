From Coq Require Import List.
Import ListNotations.

Require Import mathcomp.ssreflect.seq.

From stdpp Require Import -(notations) list_numbers.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Functor Monads Traversable.
Import FunctorNotation MonadNotation.
Local Open Scope monad.

From Wasm Require datatypes operations.

From RichWasm Require term.
From RichWasm.compiler Require Import util.

Module R := RichWasm.term.
Module W. Include datatypes <+ operations. End W.

Inductive LayoutMode :=
  | LMWords
  | LMNative.

Definition translate_int_type (ty : R.IntType) : W.value_type :=
  match ty with
  | R.i32 => W.T_i32
  | R.i64 => W.T_i64
  end.

Definition translate_float_type (ty : R.FloatType) : W.value_type :=
  match ty with
  | R.f32 => W.T_f32
  | R.f64 => W.T_f64
  end.

Definition translate_num_type (ty : R.NumType) : W.value_type :=
  match ty with
  | R.Int _ int_ty => translate_int_type int_ty
  | R.Float float_ty => translate_float_type float_ty
  end.

Definition translate_kind_var (k : R.KindVar) : list W.value_type :=
  match k with
  | R.SIZE _ _ => [W.T_i32]
  | _ => []
  end.

Fixpoint translate_type (ty : R.Typ) : list W.value_type :=
  match ty with
  | R.Num num_ty => [translate_num_type num_ty]
  | R.TVar _ => [W.T_i32]
  | R.Unit => []
  | R.ProdT tys => flat_map translate_type tys
  | R.CoderefT _ => [W.T_i32]
  | R.Rec _ ty' => translate_type ty'
  | R.PtrT _ => [W.T_i32]
  | R.ExLoc _ ty' => translate_type ty'
  | R.OwnR _ => []
  | R.CapT _ _ _ => []
  | R.RefT _ _ _  => [W.T_i32]
  end.

Definition translate_arrow_type (ty : R.ArrowType) : W.function_type :=
  let '(R.Arrow tys1 tys2) := ty in
  let tys1' := flat_map translate_type tys1 in
  let tys2' := flat_map translate_type tys2 in
  W.Tf tys1' tys2'.

Definition translate_fun_type (ty : R.FunType) : W.function_type :=
  let '(R.FunT ks (R.Arrow tys1 tys2)) := ty in
  let ks' := flat_map translate_kind_var ks in
  let tys1' := flat_map translate_type tys1 in
  let tys2' := flat_map translate_type tys2 in
  W.Tf (ks' ++ tys1') tys2'.

Definition type_words (ty : R.Typ) : nat :=
  sum_list_with W.words_t (translate_type ty).

Definition type_layout_length (layout : LayoutMode) (ty : R.Typ) :=
  match layout with
  | LMWords => type_words ty
  | LMNative => length (translate_type ty)
  end.

Fixpoint size_upper_bound (ctx : list (list R.Size * list R.Size)) (sz : R.Size) : error + nat :=
  match sz with
  | R.SizeConst c => inr c
  | R.SizePlus sz1 sz2 =>
      ub1 <- size_upper_bound ctx sz1;;
      ub2 <- size_upper_bound ctx sz2;;
      inr (ub1 + ub2)
  | R.SizeVar _ => inl ETodo
  end.

Definition struct_field_offset (fields : list (R.Typ * R.Size)) (idx : nat) : error + R.Size :=
  let fix go fs i :=
    match fs, i with
    | _, 0 => inr (R.SizeConst 0)
    | (_, sz) :: fs', i' => R.SizePlus sz <$> go fs' i'
    | [], _ => inl (EIndexOutOfBounds idx)
    end
  in
  go fields idx.

Definition struct_fields (ty : R.Typ) : option (list (R.Typ * R.Size)) :=
  match ty with
  | R.RefT _ _ (R.StructType fields) => Some fields
  | _ => None
  end.

Definition array_elem (ty : R.Typ) : option R.Typ :=
  match ty with
  | R.RefT _ _ (R.ArrayType ty') => Some ty'
  | _ => None
  end.

Definition find_refs (layout : LayoutMode) (ty : R.Typ) : list W.immediate :=
  let fix go ty i :=
    match ty with
    | R.Num _
    | R.Unit
    | R.CoderefT _
    | R.PtrT _
    | R.OwnR _
    | R.CapT _ _ _ => []
    | R.ProdT tys =>
        snd (foldl (fun '(j, idxs) ty' => (j + type_layout_length layout ty', idxs ++ go ty' j))
                   (i, [])
                   tys)
    | R.Rec _ ty'
    | R.ExLoc _ ty' => go ty' i
    | R.TVar _
    | R.RefT _ _ _ => [i]
    end in
  go ty 0.
