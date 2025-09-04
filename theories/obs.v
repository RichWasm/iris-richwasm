(* trap observations *)
Inductive obs :=
| Run (* no trap occurred *)
| Bail (* acceptable trap occurred *)
| Crash. (* unacceptable trap occurred *)
