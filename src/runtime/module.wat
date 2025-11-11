(module
  (func (export "mmalloc") (param i32) (result i32)
    unreachable)

  (func (export "gcalloc") (param i32) (result i32)
    unreachable)

  (; table.set was only introduced in wasm 2.0 but that's fine since our runtime supports it.
     if we were strictly using wasm 1.0 this would be implemented using the host language. ;)
  (func (export "tableset") (param i32 i32) (result)
    unreachable
    (;  table.set   ;))

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

  (memory $mmmem (export "mmmem") 0)
  (memory $gcmem (export "gcmem") 0))
