open! Core

let simple_tests =
  [
    ( "simple cases",
      {|
        ((imports ())
         (functions
          (((typ (FunctionType () () ((Num (Int I32)))))
            (locals ())
            (body
             ((NumConst (Int I32) -1)
              (Inject 0
               ((Num (Int I32)) (Num (Int I32)) (Num (Int I32)) (Num (Int I32))))
              (Case (ValType ((Num (Int I32)))) InferFx
               ((Drop (NumConst (Int I32) 0))
                (Drop (NumConst (Int I32) 1))
                (Drop (NumConst (Int I32) 2))
                (Drop (NumConst (Int I32) 3)))))))))
         (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "0" );
    (* ( "boxed sum",
      {| 
      ((imports ())
       (functions
        (((typ (FunctionType () () ((Num (Int I32)))))
          (locals
           ((Atom Ptr)
            (Sum ((Atom I32) (Atom I32)))
            (Sum ((Atom I32) (Atom I32)))
            (Atom I32) (Atom I32)))
          (body
           ((NumConst (Int I32) 7)
            (Inject 0 ((Num (Int I32)) (Num (Int I32))))
            (New MM)
            (Load (Path ()) Move)
            (LocalSet 1)
            Drop 
            (LocalGet 1 Move)
            (Case (ValType ((Num (Int I32)))) InferFx
             ((Nop)
              (Nop))))))))
       (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "7" ); *)
  ]
