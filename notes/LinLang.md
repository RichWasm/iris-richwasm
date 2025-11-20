# Lin Lang

Simple linear lambda calculus with 32-bit integers and n-ary tuples.

## Grammar

```
τ ::=
    | int
    | x
    | (τ₁ ⊸ τ₂)
    | (τ₁ ⊗ ... ⊗ τₙ)
    | (τ₁ ⊕ ... ⊕ τₙ)
    | (rec x τ)
    | (ref τ)

binop := + | - | × | ÷

v ::=
    | n
    | x
    | (λ (x : τ₁) : τ₂ . e)
    | (v₁, ..., vₙ)
    | (inj i e : τ)
    | (fold τ e)
    | (app v₁ v₂)
    | (let (x : τ) = e₁ in e₂)
    | (split (x₁ : τ₁) ... (xₙ : τₙ) = e₁ in e₂)
    | (cases v (case (x₁ : τ₁) e₁) ... (case (xₙ : τₙ) eₙ))
    | (unfold τ e)
    | (if0 e₁ then e₂ else e₃)
    | (e₁ binop e₂)
    | (new e)
    | (swap e₁ e₂)
    | (free e)

im := (import τ as x)
fn := ([export] fun x₁ (x₂ : τ₁) : τ₂ . e)

m := im* fn* [e]
```

n.b. the grammar is in Monadic Normal Form

## Phases

- sexp-based parser
- de bruijn index
- closure conversion
- typechecker/elaboration
- code gen into RichWasm

## Type System

TODO

## Notes

### 2025-09-15

RW existentials have been changed since the prev paper, and now don't need to always be on the
stack--might mean that RW will need to be tweaked for the lin-lang compiler.

### 2025-09-18

Make calling convention uniform

just make n-ary tuples

### 2025-09-25

All calls are indirect since that is the most general case

All functions get placed into the table, and map fname to idx.

When typing tuples, `ref` propagates linearity to outer.

Linear local.get consumes local, annotation needs to reflect this.

### 2025-09-26

Language changes:
- remove globals (only have top level *functions*)
- add recursive types and sum types
- add recursive functions

### 2025-09-30

closures must be boxed to maintain a uniform kind

---

See if annotating local effects is strictly needed? Can this be inferred?

See what WAT does with block types.

### 2025-10-02

Remove MNF.

Add dedicated `fix` to the language.

### 2025-10-03

Write Pretty Printer for annotated AST (to use in Rocq)

See if LocalEffects can be entirely inferred.

If time, eventually check linearity in the LL type checker.

### 2025-10-09

will need to serialize sums before allocating them -- this avoids the rwasm -> wasm compiler having to implicitly casing...

# Thoughts for later

## Tail calls

- top level functions need 0-sized allocations every time
- also call-indirect when call could work

