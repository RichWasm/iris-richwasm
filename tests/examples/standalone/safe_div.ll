(fun safe_div (p : (int ⊗ int)) : (int ⊕ ()) .
  (split (x : int) (y : int) = p in
  (if0 y then
    (inj 1 () : (int ⊕ ()))
  else
    (let (q : int) = (x ÷ y) in
    (inj 0 q : (int ⊕ ()))))))
(fun from_either (e : (int ⊕ ())) : int .
  (cases e
    (case (ok : int) ok)
    (case (err : ()) 0)))
(let (r : (int ⊕ ())) = (safe_div (10, 0)) in
(app from_either r))
