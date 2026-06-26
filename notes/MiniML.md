# MiniML

System F with refs, universals, _no existentials_, products, sums.

## Grammar

```
τ ::=
    | int
    | x
    | ((x₁ ... xₙ) τ₁ -> τ₂)
    | (* τ₁ ... τₙ)
    | (*# τ₁ ... τₙ)
    | (+ τ₁ ... τₙ)
    | (+# τ₁ ... τₙ)
    | (rec (x) τ)
    | (ref τ)
    | (lin-ref τ)

binop := + | - | * | /

e ::=
    | n
    | x
    | (let (x : τ) e₁ e₂)
    | (fun (x₁ ... xₙ) (x : τ₁) : τ₂ e)
    | (lam (x₁ ... xₙ) (x : τ₁) : τ₂ e)
    | (app f (τ₁ ... τₙ) e)
    | (tup e₁ ... eₙ)
    | (tup# e₁ ... eₙ)
    | (proj i e)                               ; boxed
    | (split# ((x₁ : τ₁) ... (xₙ : τₙ)) e₁ e₂) ; unboxed
    | (inj i e : τ)
    | (inj# i e : τ)
    | (cases e ((x₁ : τ₁) e₁) ... ((xₙ : τₙ) eₙ))
    | (case# e ((x₁ : τ₁) e₁) ... ((xₙ : τₙ) eₙ))
    | (fold τ e)
    | (unfold e)
    | (if c t e)
    | (op binop e₁ e₂)
    | (new e)
    | (! e)
    | (assign e₁ e₂)
    | (swap e₁ e₂)

im := (import (x : τ))
fn := (export (x : τ) e)
    | (private (x : τ) e)

m := im* fn* [e]
```

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

Unboxed tuples `(*# τ₁ ... τₙ)` / `(tup# e₁ ... eₙ)` compile to RichWasm `Prod`
instead of a boxed `Struct` (and unboxed sums `(+# τ₁ ... τₙ)` / `(inj# i e : τ)`
to RichWasm `Sum` instead of a boxed `Variant`) -- which is a departure from the
uniform `ptr` representation. We let the RichWasm typechecker police errors, and
since they cannot instantiate type variables, polymorphism stays uniform. Their
only eliminators are `split#` and `case#` since we'd otherwise need to drop other
elements of tuple (there are not stack references).
