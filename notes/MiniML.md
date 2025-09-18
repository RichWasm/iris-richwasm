# MiniML

System F with refs, universals, _no existentials_, products, sums.

## Control Flow

Restrict language to be in a monadic normal form.

```plain
e ::= v1 v2 | let x = e1 in e2
```

to prevent ANF-like things from happening.

Combine both big and little lambda into one syntactic form.

## To Read

Review Existing OCaml implementation and see what can be reused

Read System F to tal paper (target for closure conversion must have existentials)

Read Linking types

## TODO

Make functions unary
