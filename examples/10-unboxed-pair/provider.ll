(export fun mk (i : int) : (ref (prod int int)) .
  (let (r : (ref (prod int int))) = (new (i, 0)) in
   (split (r2 : (ref (prod int int))) (old : (prod int int)) = (swap r (i, (i + 1))) in
    r2)))
