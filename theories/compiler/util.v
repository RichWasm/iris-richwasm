From ExtLib.Structures Require Import Monads.

Require Import stdpp.list.

From RichWasm Require Import prelude syntax.
From RichWasm.compiler Require Import prelude codegen.

Definition get_locals_w : list W.localidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_get_local ∘ localimm).

Definition set_locals_w : list W.localidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_set_local ∘ localimm) ∘ @rev _.

Definition get_globals_w : list W.globalidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_get_global ∘ globalimm).

Definition set_globals_w : list W.globalidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_set_global ∘ globalimm) ∘ @rev _.

Definition wlalloc (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
  wl ← get;
  put (wl ++ [ty]);;
  ret (W.Mk_localidx (fe_wlocal_offset fe + length wl)).

Definition save_stack1 (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
  i ← wlalloc fe ty;
  emit (W.BI_set_local (localimm i));;
  ret i.

Definition save_stack_w (fe : function_env) (tys : W.result_type) : codegen (list W.localidx) :=
  ixs ← mapM (wlalloc fe) tys;
  set_locals_w ixs;;
  ret ixs.

Definition save_stack (fe : function_env) (ιs : list primitive_rep) : codegen (list W.localidx) :=
  save_stack_w fe (map translate_prim_rep ιs).

Definition restore_stack : list W.localidx -> codegen unit := get_locals_w.
