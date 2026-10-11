(let (r : (ref (sum int int))) = (new (inj 0 7 : (sum int int))) in
 (let (s : (sum int int)) = (free r) in
  (cases s
    (case (x : int) x)
    (case (y : int) y))))
