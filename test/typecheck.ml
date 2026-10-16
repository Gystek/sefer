open Sefer
open Sefer.Location
open Sefer.Infer
open Sefer.Expr

let l = { f = "test"; s = (0, 0); e = (0, 0) }
let le e = { ann = (l, None); exp = e }
let lte t e = { ann = (l, Some t); exp = e }

(* let typ_testable = Alcotest.testable Type.pp Type.equal *)

(* let expr_testable = Alcotest.testable pp equal *)

let location_testable = Alcotest.testable Location.pp Location.equal
let locexpr_testable = Alcotest.testable pp_locexpr equal_locexpr
let tcerror_testable = Alcotest.testable pp_tcerror equal_tcerror

let result_tcerror_locexpr_testable =
  Alcotest.result locexpr_testable
    (Alcotest.pair location_testable tcerror_testable)

(* TODO: copy sound-eager tests *)

let test_mono_if () =
  let raw =
    le
      (If
         ( le (Expr.Literal (Expr.Boolean true)),
           le (Abstraction ([ ("x", None) ], le (Variable "x"))),
           le (Abstraction ([ ("x", None) ], le (Variable "x"))) ))
  in
  let exp =
    Ok
      (lte
         (Type.Forall (0, Type.Arrow (Type.Var 0, Type.Var 0)))
         (If
            ( lte Type.Boolean (Expr.Literal (Expr.Boolean true)),
              lte
                (Type.Forall (0, Type.Arrow (Type.Var 0, Type.Var 0)))
                (Abstraction
                   ( [ ("x", Some (Type.Var 0)) ],
                     lte (Type.Var 0) (Variable "x") )),
              lte
                (Type.Forall (1, Type.Arrow (Type.Var 1, Type.Var 1)))
                (Abstraction
                   ( [ ("x", Some (Type.Var 1)) ],
                     lte (Type.Var 1) (Variable "x") )) )))
  and got = run_tc (init_tc ()) raw in
  Format.printf "raw: %a\n" pp raw.exp;
  Format.printf "exp: %a\n" pp_locexpr (Result.get_ok exp);
  Format.printf "got: %a\n" pp_locexpr (Result.get_ok got);
  Alcotest.check result_tcerror_locexpr_testable "same inference" exp got

let test_poly_simple () =
  let raw = le (Abstraction ([ ("x", None) ], le (Variable "x"))) in
  let exp =
    Ok
      (lte
         (Type.Forall (0, Type.Arrow (Type.Var 0, Type.Var 0)))
         (Abstraction
            ([ ("x", Some (Type.Var 0)) ], lte (Type.Var 0) (Variable "x"))))
  and got = run_tc (init_tc ()) raw in
  Format.printf "raw: %a\n" pp raw.exp;
  Format.printf "exp: %a\n" pp_locexpr (Result.get_ok exp);
  Format.printf "got: %a\n" pp_locexpr (Result.get_ok got);
  Alcotest.check result_tcerror_locexpr_testable "same inference" exp got

let test_poly_complex () =
  let raw =
    le
      (Abstraction
         ( [ ("x", None) ],
           le
             (Application
                ( le (Abstraction ([ ("y", None) ], le (Variable "y"))),
                  [
                    le
                      (Application
                         ( le
                             (Abstraction
                                ([ ("a", None); ("b", None) ], le (Variable "a"))),
                           [
                             le
                               (Tuple
                                  [
                                    le (Literal (Integer 5)); le (Variable "x");
                                  ]);
                           ] ));
                  ] )) ))
  in
  let exp =
    Ok
      (lte
         (Sefer.Type.Forall
            ( 0,
              Sefer.Type.Forall
                ( 3,
                  Sefer.Type.Arrow
                    ( Sefer.Type.Var 0,
                      Sefer.Type.Arrow
                        ( Sefer.Type.Var 3,
                          Sefer.Type.Tuple
                            [ Sefer.Type.Integer; Sefer.Type.Var 0 ] ) ) ) ))
         (Abstraction
            ( [ ("x", Some (Sefer.Type.Var 0)) ],
              lte
                (Sefer.Type.Forall
                   ( 3,
                     Sefer.Type.Forall
                       ( 0,
                         Sefer.Type.Arrow
                           ( Sefer.Type.Var 3,
                             Sefer.Type.Tuple
                               [ Sefer.Type.Integer; Sefer.Type.Var 0 ] ) ) ))
                (Application
                   ( lte
                       (Sefer.Type.Forall
                          ( 3,
                            Sefer.Type.Forall
                              ( 0,
                                Sefer.Type.Arrow
                                  ( Sefer.Type.Arrow
                                      ( Sefer.Type.Var 3,
                                        Sefer.Type.Tuple
                                          [
                                            Sefer.Type.Integer; Sefer.Type.Var 0;
                                          ] ),
                                    Sefer.Type.Arrow
                                      ( Sefer.Type.Var 3,
                                        Sefer.Type.Tuple
                                          [
                                            Sefer.Type.Integer; Sefer.Type.Var 0;
                                          ] ) ) ) ))
                       (Abstraction
                          ( [ ("y", Some (Sefer.Type.Var 1)) ],
                            lte
                              (Sefer.Type.Forall
                                 ( 3,
                                   Sefer.Type.Forall
                                     ( 0,
                                       Sefer.Type.Arrow
                                         ( Sefer.Type.Var 3,
                                           Sefer.Type.Tuple
                                             [
                                               Sefer.Type.Integer;
                                               Sefer.Type.Var 0;
                                             ] ) ) ))
                              (Variable "y") )),
                     [
                       lte
                         (Sefer.Type.Forall
                            ( 3,
                              Sefer.Type.Forall
                                ( 0,
                                  Sefer.Type.Arrow
                                    ( Sefer.Type.Var 3,
                                      Sefer.Type.Tuple
                                        [ Sefer.Type.Integer; Sefer.Type.Var 0 ]
                                    ) ) ))
                         (Application
                            ( lte
                                (Sefer.Type.Forall
                                   ( 0,
                                     Sefer.Type.Forall
                                       ( 3,
                                         Sefer.Type.Arrow
                                           ( Sefer.Type.Tuple
                                               [
                                                 Sefer.Type.Integer;
                                                 Sefer.Type.Var 0;
                                               ],
                                             Sefer.Type.Arrow
                                               ( Sefer.Type.Var 3,
                                                 Sefer.Type.Tuple
                                                   [
                                                     Sefer.Type.Integer;
                                                     Sefer.Type.Var 0;
                                                   ] ) ) ) ))
                                (Abstraction
                                   ( [
                                       ("a", Some (Sefer.Type.Var 2));
                                       ("b", Some (Sefer.Type.Var 3));
                                     ],
                                     lte
                                       (Sefer.Type.Forall
                                          ( 0,
                                            Sefer.Type.Tuple
                                              [
                                                Sefer.Type.Integer;
                                                Sefer.Type.Var 0;
                                              ] ))
                                       (Variable "a") )),
                              [
                                lte
                                  (Sefer.Type.Forall
                                     ( 0,
                                       Sefer.Type.Tuple
                                         [
                                           Sefer.Type.Integer; Sefer.Type.Var 0;
                                         ] ))
                                  (Tuple
                                     [
                                       lte Sefer.Type.Integer
                                         (Literal (Integer 5));
                                       lte
                                         (Sefer.Type.Forall (0, Sefer.Type.Var 0))
                                         (Variable "x");
                                     ]);
                              ] ));
                     ] )) )))
  and got = run_tc (init_tc ()) raw in
  Format.printf "raw: %a\n" pp raw.exp;
  Format.printf "exp: %a\n" pp_locexpr (Result.get_ok exp);
  Format.printf "got: %a\n" pp_locexpr (Result.get_ok got);
  Alcotest.check result_tcerror_locexpr_testable "same inference" exp got

let () =
  Alcotest.run "typecheck"
    [
      ("mono", [ Alcotest.test_case "if" `Quick test_mono_if ]);
      ( "poly",
        [
          Alcotest.test_case "simple" `Quick test_poly_simple;
          Alcotest.test_case "complex" `Quick test_poly_complex;
        ] );
    ]
