(module
  (table $table (export "table") 0 funcref)

  (global (export "tablenext") (mut i32) (i32.const 0))

  (global $mm_ptr (mut i32) (i32.const 1))
  (global $gc_ptr (mut i32) (i32.const 65539))
  (global $root_ptr (mut i32) (i32.const 0))
  (global $mm_end (mut i32) (i32.const 0))
  (global $gc_end (mut i32) (i32.const 65536))

  (; gc roots are first page of gc mem ;)
  (global $root_end i32 (i32.const 65535))
  (global $page_size i32 (i32.const 65536))

  (memory $mmmem (export "mmmem") 0)
  (memory $gcmem (export "gcmem") 1) (; pre-allocate root section ;)

  (func (export "registerroot") (param i32) (result i32)
    (local $old i32)
    (local $new i32)
    global.get $root_ptr
    local.tee $old
    i32.const 4
    i32.add
    local.tee $new
    global.get $root_end
    i32.ge_s
    (if (then unreachable) (else))
    local.get $new
    global.set $root_ptr
    local.get $old)

  (func (export "unregisterroot") (param i32) (result)
    nop)

  (func (export "mmalloc") (param $size i32) (result i32)
    (local $diff i32)
    (local $quotient i32)
    (local $grown i32)
    (local $raw_next i32)
    local.get $size
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
        global.set $mm_end
        drop)
      (else))
    global.get $mm_ptr
    global.get $mm_ptr
    local.get $size
    i32.add
    i32.const 1 ;; 0b01
    call $align
    global.set $mm_ptr)

  (func (export "gcalloc") (param $size i32) (result i32)
    (local $diff i32)
    (local $quotient i32)
    (local $grown i32)
    (local $raw_next i32)
    local.get $size
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
        global.set $gc_end
        drop)
      (else))
    global.get $gc_ptr
    global.get $gc_ptr
    local.get $size
    i32.add
    i32.const 3 ;; 0b11
    call $align
    global.set $gc_ptr)

  (func (export "free") (param i32) (result)
    nop)

  (func (export "setflag") (param i32 i32 i32) (result)
    nop)

  (func $align (param $value i32) (param $alignment i32) (result i32)
    ;; internal helper to align the next pointer
    local.get $value
    local.get $alignment
    local.get $value
    i32.sub
    i32.const 3
    i32.and
    i32.add))
