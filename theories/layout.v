From stdpp Require Import base list.

Require Import RichWasm.syntax.

Definition kind_rep (κ : kind) : option representation :=
  match κ with
  | VALTYPE ρ _ => Some ρ
  | MEMTYPE _ _ => None
  end.

Definition kind_size (κ : kind) : option size :=
  match κ with
  | VALTYPE _ _ => None
  | MEMTYPE σ _ => Some σ
  end.

Definition ref_flag_le (ξ ξ' : ref_flag) : bool :=
  match ξ, ξ' with
  | NoRefs, _
  | GCRefs, GCRefs
  | GCRefs, AnyRefs
  | AnyRefs, AnyRefs => true
  | _, _ => false
  end.

Definition ref_flag_lub2 (ξ1 ξ2 : ref_flag) : ref_flag :=
  match ξ1 with
  | NoRefs => ξ2
  | GCRefs =>
      match ξ2 with
      | NoRefs => GCRefs
      | _ => ξ2
      end
  | AnyRefs => AnyRefs
  end.

Definition ref_flag_lub (ξs : list ref_flag) : ref_flag :=
  foldr ref_flag_lub2 NoRefs ξs.

Definition kind_of_num (nt : num_type) : kind :=
  match nt with
  | IntT I32T => VALTYPE (AtomR I32R) NoRefs
  | IntT I64T => VALTYPE (AtomR I64R) NoRefs
  | FloatT F32T => VALTYPE (AtomR F32R) NoRefs
  | FloatT F64T => VALTYPE (AtomR F64R) NoRefs
  end.

Definition mem_ref_flag (μ : memory) : ref_flag :=
  match μ with
  | BaseM MemGC => GCRefs
  | _ => AnyRefs
  end.

(* Kinds are no longer cached on [type] nodes -- this recomputes the
   (principal) kind of a type bottom-up in a context of kinds for its
   free type variables, mirroring [has_kind]. *)
Fixpoint type_kind (κs : list kind) (τ : type) : option kind :=
  match τ with
  | VarT t => κs !! t
  | I31T => Some (VALTYPE (AtomR PtrR) NoRefs)
  | NumT nt => Some (kind_of_num nt)
  | SumT τs =>
      κs' ← mapM (type_kind κs) τs;
      ρs ← mapM kind_rep κs';
      Some (VALTYPE (SumR ρs) (ref_flag_lub (map kind_ref_flag κs')))
  | VariantT τs =>
      κs' ← mapM (type_kind κs) τs;
      σs ← mapM kind_size κs';
      Some (MEMTYPE (SumS σs) (ref_flag_lub (map kind_ref_flag κs')))
  | ProdT τs =>
      κs' ← mapM (type_kind κs) τs;
      ρs ← mapM kind_rep κs';
      Some (VALTYPE (ProdR ρs) (ref_flag_lub (map kind_ref_flag κs')))
  | StructT τs =>
      κs' ← mapM (type_kind κs) τs;
      σs ← mapM kind_size κs';
      Some (MEMTYPE (ProdS σs) (ref_flag_lub (map kind_ref_flag κs')))
  | RefT μ _ τ =>
      κ ← type_kind κs τ;
      match κ with
      | MEMTYPE _ _ => Some (VALTYPE (AtomR PtrR) (mem_ref_flag μ))
      | VALTYPE _ _ => None
      end
  | CodeRefT _ => Some (VALTYPE (AtomR I32R) NoRefs)
  | SerT τ =>
      κ ← type_kind κs τ;
      match κ with
      | VALTYPE ρ ξ => Some (MEMTYPE (RepS ρ) ξ)
      | MEMTYPE _ _ => None
      end
  | PlugT ρ => Some (VALTYPE ρ NoRefs)
  | SpanT σ => Some (MEMTYPE σ NoRefs)
  | RecT κ _
  | ExistsMemT κ _
  | ExistsRepT κ _
  | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => Some κ
  end.

Definition int_type_arep (νi : int_type) : atomic_rep :=
  match νi with
  | I32T => I32R
  | I64T => I64R
  end.

Definition int_type_type (νi : int_type) : type :=
  NumT (IntT νi).

Definition float_type_arep (νf : float_type) : atomic_rep :=
  match νf with
  | F32T => F32R
  | F64T => F64R
  end.

Definition float_type_type (νf : float_type) : type :=
  NumT (FloatT νf).

Definition num_type_type (ν : num_type) : type :=
  match ν with
  | IntT νi => int_type_type νi
  | FloatT νf => float_type_type νf
  end.

Definition type_i31 : type := I31T.
Definition type_i32 : type := int_type_type I32T.
Definition type_i64 : type := int_type_type I64T.
Definition type_f32 : type := float_type_type F32T.
Definition type_f64 : type := float_type_type F64T.
Definition type_plug (ρ : representation) : type := PlugT ρ.
Definition type_span (σ : size) : type := SpanT σ.

(* Fact: If |- NumT ν : κ, then Some [num_type_rep ν] = type_rep (NumT ν). *)
Definition num_type_arep (ν : num_type) : atomic_rep :=
  match ν with
  | IntT νi => int_type_arep νi
  | FloatT νf => float_type_arep νf
  end.

Definition prim_to_arep (η : primitive) : atomic_rep :=
  match η with
  | I32P => I32R
  | I64P => I64R
  | F32P => F32R
  | F64P => F64R
  end.

Definition type_plug_prim (ηs : list primitive) : type :=
  type_plug (ProdR (map (AtomR ∘ prim_to_arep) ηs)).

Definition type_rep (κs : list kind) (τ : type) : option representation :=
  type_kind κs τ ≫= kind_rep.

Definition type_size (κs : list kind) (τ : type) : option size :=
  type_kind κs τ ≫= kind_size.

Definition arep_size (ι : atomic_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Definition areps_size : list atomic_rep -> nat :=
  list_sum ∘ map arep_size.

Class Env E :=
  {
    lookup_mem : E -> nat -> option base_memory;
    lookup_rep : E -> nat -> option (list atomic_rep);
    lookup_size : E -> nat -> option nat;
  }.

Definition eval_mem `{Env E} (env : E) (μ : memory) : option base_memory :=
  match μ with
  | VarM x => lookup_mem env x
  | BaseM bm => Some bm
  end.

Fixpoint eval_rep `{Env E} (env : E) (ρ : representation) : option (list atomic_rep) :=
  match ρ with
  | VarR x => lookup_rep env x
  | SumR ρs => cons I32R ∘ @concat _ <$> mapM (eval_rep env) ρs
  | ProdR ρs => @concat _ <$> mapM (eval_rep env) ρs
  | AtomR ι => Some [ι]
  end.

Definition eval_rep_prim `{Env E} (env : E) (ρ : representation) : option (list primitive) :=
  map arep_to_prim <$> eval_rep env ρ.

Definition eval_rep_size `{Env E} (env : E) (ρ : representation) : option nat :=
  areps_size <$> eval_rep env ρ.

Fixpoint eval_size `{Env E} (env : E) (σ : size) : option nat :=
  match σ with
  | VarS x => lookup_size env x
  | SumS σs =>
      ns ← mapM (eval_size env) σs;
      Some (1 + list_max ns)
  | ProdS σs => list_sum <$> mapM (eval_size env) σs
  | RepS ρ => list_sum ∘ map arep_size <$> eval_rep env ρ
  | ConstS n => Some n
  end.

Definition eval_kind `{Env E} (env : E) (κ : kind) : option skind :=
  match κ with
  | VALTYPE ρ ξ =>
      sρ ← eval_rep env ρ;
      mret $ SVALTYPE sρ ξ
  | MEMTYPE σ ξ =>
      n ← eval_size env σ;
      mret $ SMEMTYPE n ξ
  end.

Definition sum_offset `{Env E} (env : E) (ρs : list representation) (i : nat) : option nat :=
  ιss ← mapM (eval_rep env) (take i ρs);
  Some (length (concat ιss)).

(* empty_env is a type of environments that are always empty. It is
   useful for evaluating _closed_ things. *)
Inductive empty_env : Type := EmptyEnv.

Instance empty_env_env : Env empty_env :=
  {
    lookup_mem := fun _ _ => None;
    lookup_rep := fun _ _ => None;
    lookup_size := fun _ _ => None;
  }.

(* Resolve type classes here, rather than manually in the OCaml code: *)
Definition eval_rep_prim_empty (ρ : representation) : option (list primitive) :=
  eval_rep_prim EmptyEnv ρ.
