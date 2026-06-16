# MiniML

System F with refs, universals, _no existentials_, products, sums.

## Grammar

```
τ ::=
    | int
    | x
    | ((x₁ ... xₙ) τ₁ -> τ₂)
    | (* τ₁ ... τₙ)
    | (# τ₁ ... τₙ)
    | (+ τ₁ ... τₙ)
    | (rec (x) τ)
    | (ref τ)
    | (lin (ref τ))

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
    | (cases e ((x₁ : τ₁) e₁) ... ((xₙ : τₙ) eₙ))
    | (fold τ e)
    | (unfold e)
    | (if c t e)
    | (op binop e₁ e₂)
    | (new e)
    | (! e)
    | (assign e₁ e₂)

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

### Unboxed Tuples

Unboxed tuples `(# τ₁ ... τₙ)` / `(tup# e₁ ... eₙ)` compile to RichWasm `Prod`
instead of a boxed `Struct` -- which is a departure from the uniform `ptr`
representation. We let the RichWasm typechecker police errors, and since they
cannot instantiate type variables, polymorphism stays uniform. Their only
eliminator is `split#` since we'd otherwise need to drop other elements of
tuple (there are not stack references).

### Linear Refs

`(lin (ref τ))` is the linking annotation for a linear (MM, mutable) ref. A
foreign module can lend it to us (mini-ml never allocates one). 

It compiles to `Ref (Base MM) Mut (Ser ⟦τ⟧)`. Additionally the following 
operations are compiled differently in the presence of a lin ref:

- for deref (`(! r) : (# (lin (ref τ)) τ)`):
  - (notice it returns an unboxed tuple with the new reference)
  - A typical copy-load is emitted when `τ` is copyable
  - but, when the payload is itself lin it elaborates to a load-**move** that
    leaves a `Span` hole the next `assign` must refill
- for assign (`(assign r v) : (lin (ref τ))`):
  - elaborates to an in-place store

Variables whose type is `lin` (or an unboxed tuple containing one) compile as a
bare move instead of the usual move/copy/restore, so the local is left holding
a plug and RichWasm rejects any reuse (see the `lin_reuse_rejected` example).

Non-use leaks, which the affine model tolerates. A lin value *can* sit inside a
boxed tuple: a GC struct with a lin component is made `Mut` (`prod_mut`) and
`proj` pulls the component out by swapping in a same-typed dummy (`TSwap` is the
only flag-agnostic elimination -- a load can neither copy nor move a lin out of
GC memory). This is sound because a GC ref lubs its flag with its contents' (the
`KRefGC` lub), so a struct holding a lin is itself uncopyable rather than
laundering linearity behind a copyable shell. (The swap-based projection is
provisional -- the planned end state routes it through a Load-Move instead.) Lin
values still cannot instantiate `∀`s, since binders are kinded `gcrefs` and a lin
is `anyrefs`; RichWasm rejects that at the use site rather than mini-ml eagerly at
construction.
