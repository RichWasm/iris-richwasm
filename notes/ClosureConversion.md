# # Closure conversion  

usually:

```
  [[T1 -> T2]] = exist Aenv. Aenv x (Aenv -> T1 -> T2)

```
 For us, 
 ```
    exist r : rep.
        exist Aenv : VALTYPE r γ δ. 
            Aenv x (Aenv -> T1 -> T2)
            ```
  only goes on the stack if `r` is mono-rep. So we have to put it in the
  heap, which is where it was headed anyway, it's a closure.
  
We need operations for constructing these things in the heap.

    τ: MEMTYPE ζ μ δ
    RefT μ τ: VALTYPE (PrimR PtrR) γ δ

    exist r. exist Aenv : VALTYPE r γ δ. ref Aenv x (ref Aenv -> T1 -> T2)
    r |-  exist Aenv : VALTYPE r γ δ. ref Aenv x (ref Aenv -> T1 -> T2)

Another potential fix.

```
    exist r : rep.
        exist Aenv : MEMTYPE r γ δ. 
            ref Aenv x (ref Aenv -> T1 -> T2)
            ```
