# Reasoning in the codegen monad

Our compiler is a monadic computation. This makes it easier to reason
about compositionally, since it's implemented using the monad's
operations and generic combinators like ret, bind, and mapM.

Here are a few rules to follow when writing lemmas about computations
in the codegen monad so that we prove things at the right level of
generality.

## Rule 1: assume a successful run_codegen.
The codegen monad supports exceptions. Our FTLR assumes the compiler
succeeds and the compiler never catches its own errors, so you should never
need to reason about the exception case. Every lemma about a
computation `c` should take the form

```
forall wl v wl' es, 
  run_codegen c wl = inr (v, wl', es) ->
  ...
```

## Rule 2: constrain the return value.
A successful computation `c : codegen A` produces a triple `(a, wl,
es)` where `a: A`. In the conclusion of your lemma, constrain the
value of `a`. If `A` happens to be `unit`, include `a = ()` in your
postcondition. Generally try to give the most general specification
for `a` you can.

## Rule 3: constrain the output context.
Likewise, for the output state/context, try to give a general spec. This will usually look like 
```
wl' = wl ++ new_stuff,
```
where `wl` was the original context.

## Rule 4: constrain the Wasm code
For the expressions `es` written by the computation, you can either
give a syntactic postcondition or a semantic one. A syntactic
postcondition looks like the `es = es1 ++ es2` in the conclusion of
`run_codegen_bind_dist`. A semantic postcondition leaves the exact
shape of `es` unconstrained and instead gives an Iris weakest
precondition involving `es`, like the conclusion of `wp_if_c`:
```
WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
```
Notice that this adds an argument stack to the left of `es` and (if
you look at the full lemma) also expects some weakest preconditions
for the true and false branches of the code as assumptions.
