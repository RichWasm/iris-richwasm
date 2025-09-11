Require Import Stdlib.Strings.String.

Require Import RichWasm.syntax.rw.

Inductive mutability :=
| Mut
| Imm.

Record module_function :=
  { mf_type : function_type;
    mf_body : list instruction }.

Arguments module_function : clear implicits.

Record module_global :=
  { mg_type : type;
    mg_init : list instruction }.

Arguments module_global : clear implicits.

Inductive module_import_desc :=
| ImFunction (ϕ : function_type)
| ImGlobal (ω : mutability) (τ : type).

Arguments module_import_desc : clear implicits.

Record module_import :=
  { mi_name : string;
    mi_desc : module_import_desc }.

Arguments module_import : clear implicits.

Inductive module_export_desc :=
| ExFunction (n : nat)
| ExGlobal (n : nat).

Record module_export :=
  { me_name : string;
    me_desc : module_export_desc }.

Record module :=
  { m_imports : list module_import;
    m_globals : list module_global;
    m_funcs : list module_function;
    m_table : list nat;
    m_start : nat;
    m_exports : list module_export }.

Arguments module : clear implicits.
