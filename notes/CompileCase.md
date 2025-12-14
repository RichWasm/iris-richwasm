Consider the following RichWasm program:

```richwasm
(module
  (func (-> i32)
    i32.const -1
    inject 0 i32 i32 i32
    case (result i32) inferfx
      (0
        drop
        i32.const 0)
      (1
        drop
        i32.const 1)
      (2
        drop
        i32.const 2)
    end)
  (table)
  (export "_start" (func 0)))
```

Should be roughly compiled into the following Wasm:

```wat
(module
  (func $_start (export "_start") (result i32)
    (local $tag i32)
    (local $data i32)

    (local.set $tag 
      (i32.const 0))
    (local.set $data 
      (i32.const -1))
    (local.get $tag)
    (block $done (param i32) (result i32)
      (block $case0 (param i32)
        (block $case1 (param i32)
          (block $case2 (param i32)
            (br_table $case0 $case1 $case2 $case2)
            (unreachable))
          (local.get $data)
          (drop)
          (i32.const 2)
          (br $done))
        (local.get $data)
        (drop)
        (i32.const 1)
        (br $done))
      (local.get $data)
      (drop)
      (i32.const 0)
      (br $done))))
```
