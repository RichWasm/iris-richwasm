open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Syntax

let add_one_program : Module.t =
  Parse.from_string_exn
    {|
      (export fun add-one (x : int) : int .
        (x + 1))
      (app add-one 42)
    |}

let add_tup_ref : Module.t =
  Parse.from_string_exn
    {|
      (let (r : (ref int)) = (new 2) in
      (split (x1 : int) (x2 : (ref int)) = (tup 1 r) in
      (let (x2' : int) = (free x2) in
        (x1 + x2'))))
    |}

let print_10 : Module.t =
  Parse.from_string_exn
    {|
      (import (int -o ()) as print)

      (print 10)
    |}

let closure : Module.t =
  Parse.from_string_exn
    {|
      (let (x : int) = 10 in
      (app
        (lam (_ : ()) : int .
          x)
        ()))
    |}

let closure_call_var : Module.t = 
  Parse.from_string_exn {|
    (let (input : int) = 21 in
    (let (add-amount : int) = 1 in
    (app
      (lam (x : int) : int .
        (+ x add-amount))
      input)))
  |}

let factorial_program : Module.t =
  Parse.from_string_exn
    {|
      (export fun factorial (n : int) : int .
        (if0 n
          then 1
          else
            (let (n-sub1 : int) = (n - 1) in
            (let (rec-res : int) = (app factorial n-sub1) in
            (n * rec-res)))))
      (app factorial 5)
    |}

let safe_div =
  Parse.from_string_exn
    {|
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
   |}

let incr_n =
  Parse.from_string_exn
    {|
      (fun incr_1 (r : (ref int)) : (ref int) .
        (split (r1 : (ref int)) (old : int) = (swap r 0) in
        (let (new : int) = (old + 1) in
        (split (r2 : (ref int)) (_ : int) = (swap r1 new) in
        r2))))

      (export fun incr_n (p : ((ref int) ⊗ int)) : int .
        (split (r : (ref int)) (n : int) = p in
        (if0 n then
          (free r)
        else
          (let (r1 : (ref int)) = (incr_1 r) in
          (let (n1 : int) = (n - 1) in
          (incr_n (r1, n1)))))))

      (let (r0 : (ref int)) = (new 10) in
      (app incr_n (r0, 3)))
    |}

let fix_factorial =
  Parse.from_string_exn
    {|
      (let (fix : (((int -> int) -> (int -> int)) -> (int -> int))) =
        (lam (f : ((int -> int) -> (int -> int))) : (int -> int) .
          (let (omega : ((rec a (a -> (int -> int))) -> (int -> int))) =
            (lam (x : (rec a (a -> (int -> int)))) : (int -> int) .
              (let (ux : ((rec a (a -> (int -> int))) -> (int -> int))) =
                (unfold (rec a (a -> (int -> int))) x) in
              ; this doesn't work when closures are boxed!
              ; (x is now linear)
              (let (xx : (int -> int)) = (app ux x) in
              (app f xx)))) in
          (app omega (fold (rec a (a -> (int -> int))) omega)))) in
      (let (factorial : (int -> int)) =
        (app fix (lam (rec : (int -> int)) : (int -> int) .
          (lam (n : int) : int .
            (if0 n then
               1
             else
               (let (n-sub1 : int) = (- n 1) in
               (let (rec-res : int) = (app rec n-sub1) in
               (* n rec-res))))))) in
      (app factorial 5)))
    |}

(* NOTE: this doesn't work, rec types don't have lifetimes *)
let unboxed_list =
  Parse.from_string_exn
    {|
      (fun map_int
          (p : ((int -> int) * (rec α . (() + (int * α)))))
          : (rec α . (() + (int * α))) .
        (split (f : (int -> int)) (lst : (rec α . (() + (int * α)))) = p in
        (fold (rec α . (() + (int * α)))
          (cases (unfold (rec α . (() + (int * α))) lst)
            (case (nil : ())
              (inj 0 nil : (() + (int * (rec α . (() + (int * α)))))))
            (case (cons : (int * (rec α . (() + (int * α)))))
              (split (hd : int) (tl : (rec α . (() + (int * α)))) = cons in
                (inj 1 (tup (app f hd) (app map_int (f, tl)))
                  : (() + (int * (rec α . (() + (int * α))))))))))))
      (let (lst : (rec α . (() + (int * α)))) =
        (fold (rec α . (() + (int * α)))
          (inj 0 () : (() + (int * (rec α . (() + (int * α))))))) in
      (app map_int ((lam (x : int) : int . (x + 1)), lst)))
    |}

let boxed_list =
  Parse.from_string_exn
    {|
      (fun map_int
          (p : ((int -> int) * (rec α . (() + (int * (ref α))))))
          : (rec α . (() + (int * (ref α)))) .
        (split (f : (int -> int)) (lst : (rec α . (() + (int * (ref α))))) = p in
        (fold (rec α . (() + (int * (ref α))))
          (cases (unfold (rec α . (() + (int * (ref α)))) lst)
            (case (nil : ())
              (inj 0 nil : (() + (int * (ref (rec α . (() + (int * (ref α)))))))))
            (case (cons : (int * (ref (rec α . (() + (int * (ref α)))))))
              (split (hd : int) (tl : (ref (rec α . (() + (int * (ref α)))))) = cons in
                (inj 1 ((app f hd), (new (app map_int (f, (free tl)))))
                  : (() + (int * (ref (rec α . (() + (int * (ref α))))))))))))))
      (let (lst : (rec α . (() + (int * (ref α))))) =
        (fold (rec α . (() + (int * (ref α))))
          (inj 1
            (5, (new (fold (rec α . (() + (int * (ref α))))
                  (inj 0 () : (() + (int * (ref (rec α . (() + (int * (ref α)))))))))))
              : (() + (int * (ref (rec α . (() + (int * (ref α))))))))) in
      (app map_int ((lam (x : int) : int . (x + 1)), lst)))
    |}

let peano_3 =
  Parse.from_string_exn
    {|
      (fold (rec a . (() + (ref a)))
        (inj 1 (new
          (fold (rec a . (() + (ref a)))
            (inj 1 (new
              (fold (rec a . (() + (ref a)))
                (inj 1 (new
                  (fold (rec a . (() + (ref a)))
                    (inj 0 () : (() + (ref (rec a . (() + (ref a))))))))
                  : (() + (ref (rec a . (() + (ref a))))))))
              : (() + (ref (rec a . (() + (ref a))))))))
          : (() + (ref (rec a . (() + (ref a)))))))
    |}

let peano =
  Parse.from_string_exn
    {|
      (fun add
          (p : ((rec a . (() + (ref a))) * (rec a . (() + (ref a)))))
          : (rec a . (() + (ref a))) .
        (split (left : (rec a . (() + (ref a)))) (right : (rec a . (() + (ref a)))) = p in
          (cases (unfold (rec a . (() + (ref a))) left)
            (case (zero : ())
              right)
            (case (succ : (ref (rec a . (() + (ref a)))))
              (fold (rec a . (() + (ref a)))
                (inj 1 (new (app add ((free succ), right)))
                  : (() + (ref (rec a . (() + (ref a)))))))))))

      (fun from-int (int : int) : (rec a . (() + (ref a))) .
        (fold (rec a . (() + (ref a)))
          (if0 int
            (inj 0 ()
              : (() + (ref (rec a . (() + (ref a))))))
            (inj 1 (new (app from-int (int - 1)))
              : (() + (ref (rec a . (() + (ref a)))))))))

      (fun to-int (peano : (rec a . (() + (ref a)))) : int .
        (cases (unfold (rec a . (() + (ref a))) peano)
          (case (zero : ()) 0)
          (case (succ : (ref (rec a . (() + (ref a)))))
            (1 + (app to-int (free succ))))))

      (let (six   : (rec a . (() + (ref a)))) = (from-int 6) in
      (let (seven : (rec a . (() + (ref a)))) = (from-int 7) in
      (let (sum   : (rec a . (() + (ref a)))) = (add (six, seven)) in
      (to-int sum))))
    |}

let mini_zip =
  Parse.from_string_exn
    {|
      (fun add1 (x : int) : int .
        (x + 1))
      (export fun typle_add1 (x : (int * int)) : (int * int) .
        (split (x1 : int) (x2 : int) = x in
        ((add1 x1), (add1 x2))))
      (fun mini_zip_specialized (p : ((ref int) * (ref (ref int)))) : (ref (int * (ref int))) .
        (split (a : (ref int)) (b : (ref (ref int))) = p in
        (new ((free a), (free b)))))
    |}

let simple : (string * Module.t) list =
  [
    ("one", "1");
    ("flat_tuple", "(tup 1 2 3 4)");
    ("nested_tuple", "(tup (tup 1 2) (tup 3 4))");
    ("single_sum", "(inj 0 () (sum (prod)))");
    ("double_sum", "(inj 1 15 (sum (prod) int))");
    ("arith_add", "(9 + 10)");
    ("arith_sub", "(67 - 41)");
    ("arith_mul", "(42 * 10)");
    ("arith_div", "(-30 / 10)");
    ("app_ident", "((lam (x int) int x) 10)");
    ("nested_arith", "((9 + 10) * 5)");
    ("let_bind", "(let (x int) 10 x)");
  ]
  |> List.map ~f:(fun (n, s) -> (n, Parse.from_string_exn s))

let all : (string * Module.t) list =
  simple
  @ [
      ("add_one_program", add_one_program);
      ("add_tup_ref", add_tup_ref);
      ("print_10", print_10);
      ("closure", closure);
      ("closure_call_var", closure_call_var);
      ("factorial_program", factorial_program);
      ("safe_div", safe_div);
      ("incr_n", incr_n);
      ("fix_factorial[invalid]", fix_factorial);
      ("unboxed_list[invalid]", unboxed_list);
      ("boxed_list", boxed_list);
      ("peano_3", peano_3);
      ("peano", peano);
      ("mini_zip", mini_zip);
    ]
