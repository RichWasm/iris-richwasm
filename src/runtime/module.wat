(module
  (func (export "mmalloc") (param i32) (result i32)
    unreachable)

  (func (export "gcalloc") (param i32 i64) (result i32)
    unreachable)

  (func (export "free") (param i32) (result)
    nop)

  (func (export "setflag") (param i32 i32 i32) (result)
    nop)

  (func (export "registerroot") (param i32) (result i32)
    unreachable)

  (func (export "unregisterroot") (param i32) (result i32)
    nop)

  (table $table (export "table") 0 anyfunc)

  (global (export "tablenext") (mut i32)
    i32.const 0)

  (memory (export "mmmem") 0)
  (memory (export "gcmem") 0))
