# Notes

## Tasks

- [x] Compile basic numbers and their operations
- [x] Do control flow (but should be pretty similar)
- [x] Fix number instructions
- [ ] setup known module for managing memory
- [ ] use some sort of result type rather than option (excpetion type class)
- [ ] constrol flow (fix both mappings for get locals (might not be same as wasm), a local can occupy multiple slots)
    - [ ] struct set, struct swap, array and variant
    - [ ] earasable instructions

## Next Meeting:

- 

## Pointers

Polymorphic memories will need to have fat pointers (to determine which memory
we are talking about). But when the context is clear we should not be using fat
pointers and instead just use normal i32s.

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

- location is easy
- qualifiers don't get compiled directly
- types will be boxed if a function accepts abtract types
- sizes can't be erased, so sizes will just be arguments


## Memory

Need to link to a known module which manages memory.

Getlocal etc needs to account for fun sizes


