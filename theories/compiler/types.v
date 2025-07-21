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
From RichWasm.compiler Require Import error.

Module R := RichWasm.term.
Module W := Wasm.datatypes.

Inductive LayoutMode :=
  | LMWords
  | LMNative.

Definition compile_int_type (typ : R.IntType) : W.value_type :=
  match typ with
  | R.i32 => W.T_i32
  | R.i64 => W.T_i64
  end.

Definition compile_float_type (typ : R.FloatType) : W.value_type :=
  match typ with
  | R.f32 => W.T_f32
  | R.f64 => W.T_f64
  end.

Definition compile_numtyp (typ: R.NumType) : W.value_type :=
  match typ with
  | R.Int _ inttyp => compile_int_type inttyp
  | R.Float floattyp => compile_float_type floattyp
  end.

Definition compile_kindvar (κ: R.KindVar) : list W.value_type :=
  match κ with
  | R.SIZE _ _ => [W.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list R.KindVar) : list W.value_type :=
  flat_map compile_kindvar κs.

Fixpoint compile_typ (typ: R.Typ) : list W.value_type :=
  match typ with
  | R.Num ntyp => [compile_numtyp ntyp]
  | R.TVar _ => [W.T_i32]
  | R.Unit => []
  | R.ProdT typs => flatten (map compile_typ typs)
  | R.CoderefT _ => [W.T_i32]
  | R.Rec _ typ => compile_typ typ
  | R.PtrT _ => [W.T_i32]
  | R.ExLoc q typ => compile_typ typ
  | R.OwnR _ => []
  | R.CapT _ _ _ => []
  | R.RefT _ _ _  => [W.T_i32]
  end.

Definition compile_arrow_type (typ: R.ArrowType) : W.function_type :=
  match typ with
  | R.Arrow tys1 tys2 =>
    let tys1' := mapT compile_typ tys1 in
    let tys2' := mapT compile_typ tys2 in
    W.Tf (flatten tys1') (flatten tys2')
  end.

Definition compile_fun_type (ft: R.FunType) : W.function_type :=
  match ft with
  | R.FunT κs (R.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    let tys1' := flatten (mapT compile_typ tys1) in
    let tys2' := flatten (mapT compile_typ tys2) in
    W.Tf (κvs ++ tys1') tys2'
  end.

Definition words_typ (typ: R.Typ) : nat :=
  sum_list_with operations.words_t (compile_typ typ).

Definition layout_ty_length (layout : LayoutMode) (ty : R.Typ) :=
  match layout with
  | LMWords => words_typ ty
  | LMNative => length (compile_typ ty)
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

Fixpoint struct_field_offset (fields: list (R.Typ * R.Size)) (idx: nat) : error + R.Size :=
  match idx with
  | 0 => inr (R.SizeConst 0)
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => R.SizePlus sz <$> struct_field_offset fields' idx'
      | [] => inl ETodo
      end
  end.

Definition get_struct_field_types (targs : list R.Typ) (idx : nat) : error + list (R.Typ * R.Size) :=
  match lookup idx targs with
  | Some (R.RefT _ _ (R.StructType fields)) => inr fields
  | _ => inl EWrongTypeAnn
  end.

Definition get_array_elem_type (targs : list R.Typ) (idx : nat) : error + R.Typ :=
  match lookup idx targs with
  | Some (R.RefT _ _ (R.ArrayType typ)) => inr typ
  | _ => inl EWrongTypeAnn
  end.

Definition ref_indices (layout : LayoutMode) (ty : R.Typ) : list W.immediate :=
  let fix go ty i :=
    match ty with
    | R.Num _
    | R.Unit
    | R.CoderefT _
    | R.PtrT _
    | R.OwnR _
    | R.CapT _ _ _ => []
    | R.ProdT tys =>
        snd (foldl (fun '(j, is) ty' => (j + layout_ty_length layout ty', is ++ go ty' j))
                   (i, [])
                   tys)
    | R.Rec _ ty'
    | R.ExLoc _ ty' => go ty' i
    | R.TVar _
    | R.RefT _ _ _ => [i]
    end in
  go ty 0.
