(module
  ;; TODO: check order of params
  (func (export "table_set") (param i32 i32) (result)
    unreachable)

  (func (export "alloc_mm") (param i32) (result i32)
    unreachable)

  (func (export "alloc_gc") (param i32 i64) (result i32)
    unreachable)

  (func (export "free") (param i32) (result)
    unreachable)

  (func (export "registerroot") (param i32) (result i32)
    unreachable)

  (func (export "unregisterroot") (param i32) (result i32)
    unreachable)

  (table $table (export "table") 0 anyfunc)

  (global (export "table_next") (mut i32)
    i32.const 0)

  (memory (export "mem_mm") 0)
  (memory (export "mem_gc") 0))
