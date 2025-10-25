From ExtLib.Structures Require Import Monads.

Require Import stdpp.list.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude accum codegen.

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
  acc [ty];;
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

Definition case_blocks (result : W.result_type) (cases : list (nat -> codegen unit)) : codegen unit :=
  let fix go depth cases :=
    match cases with
    | [] =>
        block_c (W.Tf [W.T_i32] [])
          (block_c (W.Tf [] result) (emit (W.BI_br_table (seq 1 depth) 0));;
            emit W.BI_unreachable)
    | case :: cases' =>
        block_c (W.Tf [W.T_i32] result)
          (go (depth + 1) cases';;
           case depth;;
           emit (W.BI_br depth))
    end
  in
  go 0 cases.
