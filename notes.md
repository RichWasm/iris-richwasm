# Notes

## Pointers

Polymorphic memories will need to have fat pointers (to determine which memory
we are talking about). But when the context is clear we should not be using fat
pointers and instead just use normal i32s.

## TODO

-   Do basic numbers and their operations
-   Do control flow (but should be pretty similar)

## Questions

### Float Conversions

When converting a `nat` to a float, is it right to use the signed int converter
`float_convert_si32` and `float_convert_si64`, or should the unsigned version
be used?

I thought that the signed version should be used so that we would be able to
have negative values as well — Ari


## Good To know

- in old system:
	- size is measured in bits for the type system
	- even locations
- would like this to be changed for the new system

## Polymorphism

1. $\forall \alpha \times \rightarrow bool$
2. $i64 \times i32 \rightarrow bool$

coderef (1) [i64/\alpha] : i64\times i32 \times bool but more like (ref i64) \times i32 \rightarrow bool
coderef (2) []


## Memory

Need to link to a known module which manages memory.

Getlocal etc needs to account for fun sizes
