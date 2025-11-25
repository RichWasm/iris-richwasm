(module
  (func (export "mmalloc") (param i32) (result i32)
    (local $diff i32)
    (local $quotient i32)
    (local $grown i32)
    (local.set $diff (i32.const 0))
    (local.set $quotient (i32.const 0))
    (local.set $grown (i32.const 0))
    local.get 0
    i32.const 4
    i32.mul
    global.get $mm_ptr
    i32.add
    global.get $mm_end
    i32.sub
    local.tee $diff
    i32.const 0
    i32.ge_s
    (if
      (then
        local.get $diff
        global.get $page_size
        i32.div_s
        local.set $quotient
        local.get $diff
        global.get $page_size
        i32.rem_s
        i32.const 0
        i32.ge_s
        (if (result i32) (then i32.const 1) (else i32.const 0))
        local.get $quotient
        i32.add
        local.tee $grown
        memory.grow $mmmem
        local.get $grown
        global.get $page_size
        i32.mul
        global.get $mm_end
        i32.add
        global.set $mm_end)
      (else))
    global.get $mm_ptr)

  (func (export "gcalloc") (param i32) (result i32)
    (local $diff i32)
    (local $quotient i32)
    (local $grown i32)
    (local.set $diff (i32.const 0))
    (local.set $quotient (i32.const 0))
    (local.set $grown (i32.const 0))
    local.get 0
    i32.const 4
    i32.mul
    global.get $gc_ptr
    i32.add
    global.get $gc_end
    i32.sub
    local.tee $diff
    i32.const 0
    i32.ge_s
    (if
      (then
        local.get $diff
        global.get $page_size
        i32.div_s
        local.set $quotient
        local.get $diff
        global.get $page_size
        i32.rem_s
        i32.const 0
        i32.ge_s
        (if (result i32) (then i32.const 1) (else i32.const 0))
        local.get $quotient
        i32.add
        local.tee $grown
        memory.grow $gcmem
        local.get $grown
        global.get $page_size
        i32.mul
        global.get $gc_end
        i32.add
        global.set $gc_end)
      (else))
    global.get $gc_ptr)

  (; table.set was only introduced in wasm 2.0 but that's fine since our runtime
     supports it. if we were strictly using wasm 1.0 this would be implemented
     using the host language. ;)
  (func (export "tableset") (param i32 i32) (result)
    (; grow table if necessary to ensure index fits ;)
    (local $diff i32)
    (local.set $diff (i32.const 0))
    table.size $table (; max index + 1 ;)
    i32.const 1
    i32.sub (; max index ;)
    local.get 0
    i32.sub
    local.tee $diff
    i32.const 0
    i32.lt_s
    (if
      (then
        local.get $diff
        i32.abs
        table.grow $table)
      (else))

    (; set value ;)
    local.get 0
    local.get 1
    table.set $table)

  (func (export "free") (param i32) (result)
    nop)

  (func (export "setflag") (param i32 i32 i32) (result)
    nop)

  (func (export "registerroot") (param i32) (result i32)
    global.get $root_ptr
    copy
    i32.const 4
    i32.add
    copy
    global.get $root_end
    i32.ge_s
    (if
      (then unreachable)
      (else))
    global.set $root_ptr
    (; the initial global.get remains on the stack here ;))

  (func (export "unregisterroot") (param i32) (result i32)
    nop)

  (table $table (export "table") 0 anyfunc)

  (global (export "tablenext") (mut i32) (i32.const 0))

  (global $mm_ptr (mut i32) (i32.const 0))
  (global $gc_ptr (mut i32) (i32.const 65536))
  (global $root_ptr (mut i32) (i32.const 0))
  (global $mm_end (mut i32) (i32.const 0))
  (global $gc_end (mut i32) (i32.const 0))

  (; gc roots are first page of gc mem ;)
  (global $root_end i32 (i32.const 65535))
  (global $page_size i32 (i32.const 65536))

  (memory $mmmem (export "mmmem") 0)
  (memory $gcmem (export "gcmem") 1) (; pre-allocate root section ;))
