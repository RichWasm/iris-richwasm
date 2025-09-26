# Lin Lang

Simple linear lambda calculus with 32-bit integers and n-ary tuples.

## Grammar

```
τ ::=
    | int
    | (τ₁ ⊸ τ₂)
    | (τ₁ ⊗ ... ⊗  τₙ)
    | (ref τ)

binop := + | - | × | ÷

v ::=
    | x
    | n
    | (λ (x : τ₁) : τ₂ . e)
    | (v₁, ..., vₙ)
e ::=
    | v
    | (app v₁ v₂)
    | (let (x : τ) = e₁ in e₂)
    | (letprod (x₁ : τ₁) ... (xₙ : τₙ) = e₁ in e₂)
    | (if0 v then e₁ else e₂)
    | (v₁ binop v₂)
    | (new v)
    | (swap v₁ v₂)
    | (free v)

im := (import τ as x)
tl := ([export] let (x : τ) = e)

m := im* tl* [e]
```

n.b. the grammar is in Monadic Normal Form

## Phases

- sexp-based parser
- de bruijn index
- closure conversion
- code gen into RichWasm

## Type System

TODO

## Notes

### 2025-09-15

RW existentials have been changed since the prev paper, and now don't need to always be on the
stack--might mean that RW will need to be tweaked for the lin-lang compiler.

### 2025-09-18

Make calling convension uniform

just make n-ary tuples

### 2025-09-25

All calls are indirect since that is the most general case

All functions get placed into the table, and map fname to idx.

When typing tuples, `ref` propogrates linearity to outer.

Linear local.get consumes local, annotation needs to reflect this.

### 2025-09-26

Language changes:
- remove globals (only have top level *functions*)
- add recursive types and sum types
- add recrusive functions

