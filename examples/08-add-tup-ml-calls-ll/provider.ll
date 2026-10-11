(export fun add_tup2 (r : (ref (prod int int))) : int .
  (let (pair : (prod int int)) = (free r) in
   (split (a : int) (b : int) = pair in
    (a + b))))
