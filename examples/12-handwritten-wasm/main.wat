;; `example` from theories/examples/dup.v, proved safe there by
;; `example_dup_safe`: allocate a GC cell holding 20, register it as a root,
;; and pass the root to `dup`. The imports follow the instance the proof
;; assumes: memory 0 is gcmem, functions 0-2 are gcalloc, registerroot, dup.
(module
  (import "richwasm" "gcmem" (memory 0))
  (import "richwasm" "gcalloc" (func $gcalloc (param i32) (result i32)))
  (import "richwasm" "registerroot" (func $registerroot (param i32) (result i32)))
  (import "" "" (func $dup (param i32) (result i32)))
  (func (export "_start") (local $ref i32)
    i32.const 1
    call $gcalloc
    local.tee $ref
    i32.const 20
    i32.store offset=1 align=1
    local.get $ref
    call $registerroot
    call $dup
    drop))
