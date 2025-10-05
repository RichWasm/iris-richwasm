Require Import RichWasm.syntax.rw.

Inductive mutability :=
| Mut
| Imm.

Record global_type :=
  { gt_mut : mutability;
    gt_type : type }.

Record module_global :=
  { mg_type : global_type;
    mg_init : list instruction }.

Record module_function :=
  { mf_type : function_type;
    mf_locals : list representation;
    mf_body : list instruction }.

Inductive module_export :=
| ExFunction (n : nat)
| ExGlobal (n : nat).

Record module :=
  { m_globals_import : list global_type;
    m_globals : list module_global;
    m_funcs_import : list function_type;
    m_funcs : list module_function;
    m_table : list nat;
    m_start : option nat;
    m_exports : list module_export }.
