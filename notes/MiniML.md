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

want to show there's an ABI for MLthat allows client code to link with it

-   maybe link with a polymorphic ML function

## Example

Call an ML function from the linear side, get into ABI and data layout issues.

Polymorphic ML function that takes in some LL data

Linking types to handle passing in a linear ref into ML

One example that requires linking type, one that doesn't

Use the boxed/unboxed difference between the two languages

## Linking types

Handle `NoCopy NoDrop` in the kind (not the default ML kind translation!), some kind of foreign value annotation
