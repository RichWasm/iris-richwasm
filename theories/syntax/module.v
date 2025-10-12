Require Import RichWasm.syntax.rw.

Record module_type :=
  { mt_imports : list function_type;
    mt_exports : list function_type }.

Record module_function :=
  { mf_type : function_type;
    mf_locals : list representation;
    mf_body : list instruction }.

Record module :=
  { m_imports : list function_type;
    m_functions : list module_function;
    m_table : list nat;
    m_exports : list nat }.
