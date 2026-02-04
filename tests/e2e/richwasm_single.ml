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
    ( "cases br",
      {|
        ((imports ())
         (functions
          (((typ (FunctionType () () ((Num (Int I32)))))
            (locals ())
            (body
             (
               (Block (ValType ((Num (Int I32)))) (LocalFx ())
               (
                (Block (ValType ((Num (Int I32)))) (LocalFx ())
                 (
                  (Block (ValType ((Num (Int I32)))) (LocalFx ())
                   (
                    (NumConst (Int I32) -1)
                    (Inject 0 ((Num (Int I32))))
                    (Case (ValType ((Num (Int I32)))) (LocalFx ())
                     ((Drop (NumConst (Int I32) 67) (Br 1))))
                   )
                  )
                  (NumConst (Int I32) 0)
                  Return
                 )
                )
                (NumConst (Int I32) 42)
                Return
               )
              )
              (NumConst (Int I32) 2)
              Return
             )))))
         (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "42" );
    ( "boxed sum",
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
      "7" );
    ( "copy tuple",
      {|
        ((imports ())
         (functions
          (((typ (FunctionType () ()
              ((Prod
                ((Prod ((Num (Int I32)) (Num (Int I64))))
                 (Prod ((Num (Int I32)) (Num (Int I64)))))))))
            (locals ())
            (body
             ((NumConst (Int I32) 1)
              (NumConst (Int I64) 2)
              (Group 2)
              Copy)))))
         (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "[ 1, 2n, 1, 2n ]" );
    ( "alloc tuple mm",
      {|
        ((imports ())
         (functions
          (((typ (FunctionType () ()
              ((Prod ((Num (Int I32)) (Num (Int I64)))))))
            (locals ((Prod ((Atom I32) (Atom I64)))))
            (body
             ((NumConst (Int I32) 1)
              (NumConst (Int I64) 2)
              (Group 2)
              (New MM)
              (Load (Path ()) Move)
              (LocalSet 0)
              Drop
              (LocalGet 0 Move))))))
         (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "[ 1, 2n ]" );
    ( "alloc tuple gc",
      {|
        ((imports ())
         (functions
          (((typ (FunctionType () ()
              ((Prod ((Num (Int I32)) (Num (Int I64)))))))
            (locals ((Prod ((Atom I32) (Atom I64)))))
            (body
             ((NumConst (Int I32) 1)
              (NumConst (Int I64) 2)
              (Group 2)
              (New GC)
              (Load (Path ()) Move)
              (LocalSet 0)
              Drop
              (LocalGet 0 Move))))))
         (table ()) (exports (((name _start) (desc (Func 0))))))
      |},
      "[ 1, 2n ]" );
  ]
