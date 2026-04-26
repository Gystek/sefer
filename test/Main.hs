module Main (main) where

import Control.Monad.State
import Data.Text
import Test.Tasty
import Test.Tasty.HUnit
import qualified Sefer.Expr as Expr
import qualified Sefer.Literal as Literal
import Sefer.Location
import qualified Sefer.Pattern as Pattern
import Sefer.Statement
import qualified Sefer.Type as Type
import Sefer.Typecheck

main :: IO ()
main = defaultMain tests

defLoc :: Location
defLoc = Location { f = pack "Test file", s = (0, 0), e = (0, 0) }

tests :: TestTree
tests = testGroup "Sefer tests" [tcTests]

tcTests :: TestTree
tcTests = testGroup "Typechecker tests" [tcMonoTests, tcPolyTests]

tcMonoTests :: TestTree
tcMonoTests = testGroup "Typechecker (monomorphic) tests"
  [ testCase "integer literal" $
    let e l t = Expr.Literal (t, l) $ Literal.Integer 5
    in evalStateT (runTC $ e defLoc Nothing) (initTC [] []) @?= Right (e defLoc $ Just Type.Integer)
  , testCase "float literal" $
    let e l t = Expr.Literal (t, l) $ Literal.Floating 3.5
    in evalStateT (runTC $ e defLoc Nothing) (initTC [] []) @?= Right (e defLoc $ Just Type.Floating)
  , testCase "character literal" $
    let e l t = Expr.Literal (t, l) $ Literal.Character 'a'
    in evalStateT (runTC $ e defLoc Nothing) (initTC [] []) @?= Right (e defLoc $ Just Type.Character)
  , testCase "boolean literal" $
    let e l t = Expr.Literal (t, l) $ Literal.Boolean True
    in evalStateT (runTC $ e defLoc Nothing) (initTC [] []) @?= Right (e defLoc $ Just Type.Boolean)
  , testCase "tuple literal" $
    let e = Expr.Tuple (Nothing, defLoc) $ [ Expr.Literal (Nothing, defLoc) $ Literal.Boolean True
                                           , Expr.Literal (Nothing, defLoc) $ Literal.Integer 5
                                           ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.Tuple (Just $ Type.Tuple [Type.Boolean, Type.Integer], defLoc)
                   [ Expr.Literal (Just Type.Boolean, defLoc) $ Literal.Boolean True
                   , Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5
                   ]
                 )
  , testCase "let-in with variable" $
    let e = Expr.Let (Nothing, defLoc) (pack "x", (Nothing, defLoc))
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 5)
            (Expr.Var (Nothing, defLoc) $ pack "x")
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.Let (Just Type.Integer, defLoc) (pack "x", (Just Type.Integer, defLoc))
                  (Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5)
                  (Expr.Var (Just Type.Integer, defLoc) $ pack "x")
                 )
  , testCase "if-then-else" $
    let e = Expr.Cond (Nothing, defLoc) (Expr.Literal (Nothing, defLoc) $ Literal.Boolean False)
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 3)
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 2)
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.Cond (Just Type.Integer, defLoc) (Expr.Literal (Just Type.Boolean, defLoc) $ Literal.Boolean False)
                  (Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 3)
                  (Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 2)
                 )
  , testCase "if-then-else heterogeneity" $
    let e = Expr.Cond (Nothing, defLoc) (Expr.Literal (Nothing, defLoc) $ Literal.Boolean False)
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 3)
            (Expr.Literal (Nothing, defLoc) $ Literal.Boolean False)
    in evalStateT (runTC e) (initTC [] []) @?= Left (defLoc, UnifyFail Type.Integer Type.Boolean)
  , testCase "if-then-else bad condition" $
    let e = Expr.Cond (Nothing, defLoc) (Expr.Literal (Nothing, defLoc) $ Literal.Integer 5)
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 3)
            (Expr.Literal (Nothing, defLoc) $ Literal.Integer 2)
    in evalStateT (runTC e) (initTC [] []) @?= Left (defLoc, UnifyFail Type.Integer Type.Boolean)
  , testCase "monomorphic constructor" $
    let e = Expr.Const (Nothing, defLoc) 0 [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 2
                                           , Expr.Literal (Nothing, defLoc) $ Literal.Boolean True
                                           ]
    in evalStateT (runTC e) (initTC
                              [Constructor 0 [Type.Integer, Type.Boolean]]
                              [ADType []])
       @?= Right (Expr.Const (Just $ Type.Data 0 [], defLoc)
                  0
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 2
                  , Expr.Literal (Just Type.Boolean, defLoc) $ Literal.Boolean True
                  ])
  , testCase "if-then-else with polymorphic constructor" $
    let e = Expr.Cond (Nothing, defLoc) (Expr.Literal (Nothing, defLoc) $ Literal.Boolean True)
            (Expr.Const (Nothing, defLoc) 0 [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 2 ])
            (Expr.Const (Nothing, defLoc) 1 [ Expr.Tuple (Nothing, defLoc) [] ])
    in evalStateT (runTC e) (initTC
                             [ Constructor 0 [Type.RVar $ pack "a"] -- Just a
                             , Constructor 0 [Type.Tuple []] -- Nothing ()
                             ]
                             [ADType [pack "a"]])
       @?= Right (Expr.Cond (Just $ Type.Data 0 [Type.Integer], defLoc)
                  (Expr.Literal (Just Type.Boolean, defLoc) $ Literal.Boolean True)
                  (Expr.Const (Just $ Type.Data 0 [Type.Integer], defLoc)
                   0
                   [Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 2]
                  )
                  (Expr.Const (Just $ Type.Data 0 [Type.Integer], defLoc)
                   1
                   [Expr.Tuple (Just $ Type.Tuple [], defLoc) []]
                  )
                 )
  , testCase "pattern matching with polymorphic constructor" $
    let e = Expr.Match (Nothing, defLoc)
            (Expr.Const (Nothing, defLoc) 1 [ Expr.Tuple (Nothing, defLoc) [] ])
            [ Expr.Branch (Nothing, defLoc)
              (Pattern.Const (Nothing, defLoc) 0 [ Pattern.Binding (Nothing, defLoc)
                                                   $ pack "x"
                                                 ]
              )
              Nothing
              $ Expr.Var (Nothing, defLoc) $ pack "x"
            , Expr.Branch (Nothing, defLoc)
              (Pattern.Const (Nothing, defLoc) 1 [ Pattern.Tuple (Nothing, defLoc) [] ])
              Nothing
              $ Expr.Literal (Nothing, defLoc) $ Literal.Integer 0
            ]
    in evalStateT (runTC e) (initTC
                             [ Constructor 0 [Type.RVar $ pack "a"] -- Just a
                             , Constructor 0 [Type.Tuple []] -- Nothing ()
                             ]
                             [ADType [pack "a"]])
       @?= Right (Expr.Match (Just Type.Integer, defLoc)
                   (Expr.Const (Just $ Type.Data 0 [Type.Integer], defLoc)
                    1
                     [ Expr.Tuple (Just $ Type.Tuple [], defLoc) [] ]
                   )
                   [ Expr.Branch (Just Type.Integer, defLoc)
                     (Pattern.Const (Just $ Type.Data 0 [Type.Integer], defLoc)
                      0
                      [ Pattern.Binding (Just Type.Integer, defLoc) $ pack "x" ]
                     )
                     Nothing
                     $ Expr.Var (Just Type.Integer, defLoc) $ pack "x"
                   , Expr.Branch (Just Type.Integer, defLoc)
                     (Pattern.Const (Just $ Type.Data 0 [Type.Integer], defLoc)
                      1
                      [ Pattern.Tuple (Just $ Type.Tuple [], defLoc) [] ]
                     )
                     Nothing
                     $ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 0
                   ])
  , testCase "lambda abstraction and primitive application" $
    let e = Expr.Abs (Nothing, defLoc)
            [ (pack "x", (Nothing, defLoc))
            , (pack "y", (Nothing, defLoc))
            ]
            $ Expr.App (Nothing, defLoc)
            (Expr.Var (Nothing, defLoc) $ pack "$addInt") [ Expr.Var (Nothing, defLoc) $ pack "x"
                                                          , Expr.Var (Nothing, defLoc) $ pack "y"
                                                          ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.Abs (Just $ Type.Fun [Type.Integer, Type.Integer] Type.Integer, defLoc)
                  [ (pack "x", (Just Type.Integer, defLoc))
                  , (pack "y", (Just Type.Integer, defLoc))
                  ]
                  $ Expr.App
                   (Just Type.Integer, defLoc)
                   (Expr.Var (Just $ Type.Fun [Type.Integer, Type.Integer] Type.Integer, defLoc)
                    $ pack "$addInt"
                   )
                   [ Expr.Var (Just Type.Integer, defLoc) $ pack "x"
                   , Expr.Var (Just Type.Integer, defLoc) $ pack "y"
                   ]
                 )
  , testCase "direct application of lambda abstraction" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Abs (Nothing, defLoc)
             [ (pack "x", (Nothing, defLoc))
             , (pack "y", (Nothing, defLoc))
             ]
             $ Expr.Var (Nothing, defLoc) $ pack "x"
            )
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 3
            , Expr.Literal (Nothing, defLoc) $ Literal.Integer 2
            ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just Type.Integer, defLoc)
                  (Expr.Abs (Just $ Type.Fun [Type.Integer, Type.Integer] Type.Integer, defLoc)
                   [ (pack "x", (Just Type.Integer, defLoc))
                   , (pack "y", (Just Type.Integer, defLoc))
                   ]
                   $ Expr.Var (Just Type.Integer, defLoc) $ pack "x"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 3
                  , Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 2
                  ]
                 )
  , testCase "partial function application" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Var (Nothing, defLoc) $ pack "$addInt")
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 5 ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just $ Type.Fun [Type.Integer] Type.Integer, defLoc)
                  (Expr.Var (Just $ Type.Fun [Type.Integer, Type.Integer] Type.Integer, defLoc)
                   $ pack "$addInt"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5 ]
                 )
  ]

tcPolyTests :: TestTree
tcPolyTests = testGroup "Typechecker (polymorphic) tests" $
  [ testCase "indirect function application" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Var (Nothing, defLoc) $ pack "$id")
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 5 ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just Type.Integer, defLoc)
                  (Expr.Var (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "a", defLoc)
                   $ pack "$id"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5 ]
                 )
  , testCase "indirect partial function application" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Var (Nothing, defLoc) $ pack "$const")
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 5 ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just $ Type.Fun [Type.RVar $ pack "b"] Type.Integer, defLoc)
                  (Expr.Var (Just $ Type.Fun [Type.RVar $ pack "a", Type.RVar $ pack "b"] $ Type.RVar $ pack "a", defLoc)
                   $ pack "$const"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5 ]
                 )
  , testCase "direct function application" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Abs (Nothing, defLoc) [(pack "x", (Just $ Type.RVar $ pack "a", defLoc))]
             $ Expr.Var (Nothing, defLoc) $ pack "x"
            )
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 5 ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just Type.Integer, defLoc)
                  (Expr.Abs (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "a", defLoc)
                    [(pack "x", (Just $ Type.RVar $ pack "a", defLoc))]
                    $ Expr.Var (Just $ Type.RVar $ pack "a", defLoc) $ pack "x"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5 ]
                 )
  , testCase "direct partial function application" $
    let e = Expr.App (Nothing, defLoc)
            (Expr.Abs (Nothing, defLoc)
              [ (pack "x", (Just $ Type.RVar $ pack "a", defLoc))
              , (pack "y", (Just $ Type.RVar $ pack "b", defLoc))
              ]
             $ Expr.Var (Nothing, defLoc) $ pack "x"
            )
            [ Expr.Literal (Nothing, defLoc) $ Literal.Integer 5 ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.App (Just $ Type.Fun [Type.RVar $ pack "b"] Type.Integer, defLoc)
                  (Expr.Abs ( Just $ Type.Fun [ Type.RVar $ pack "a"
                                              , Type.RVar $ pack "b"
                                              ]
                              $ Type.RVar $ pack "a"
                            , defLoc
                            )
                   [ (pack "x", (Just $ Type.RVar $ pack "a", defLoc))
                   , (pack "y", (Just $ Type.RVar $ pack "b", defLoc))
                   ]
                    $ Expr.Var (Just $ Type.RVar $ pack "a", defLoc) $ pack "x"
                  )
                  [ Expr.Literal (Just Type.Integer, defLoc) $ Literal.Integer 5 ]
                 )
  , testCase "lambda abstraction" $
    let e = Expr.Abs (Nothing, defLoc) -- fun (f: a -> b) x y = (f x, f y)
            [ (pack "f", (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "b", defLoc))
            , (pack "x", (Just $ Type.RVar $ pack "a", defLoc))
            , (pack "y", (Just $ Type.RVar $ pack "a", defLoc))
            ]
            $ Expr.Tuple (Nothing, defLoc)
            [ Expr.App (Nothing, defLoc)
              (Expr.Var (Nothing, defLoc) $ pack "f")
              [Expr.Var (Nothing, defLoc) $ pack "x"]
            , Expr.App (Nothing, defLoc)
              (Expr.Var (Nothing, defLoc) $ pack "f")
              [Expr.Var (Nothing, defLoc) $ pack "x"]
            ]
    in evalStateT (runTC e) (initTC [] [])
       @?= Right (Expr.Abs ( Just $ Type.Fun [ Type.Fun [ Type.RVar $ pack "a"] $ Type.RVar $ pack "b"
                                             , Type.RVar $ pack "a"
                                             , Type.RVar $ pack "a"
                                             ]
                             $ Type.Tuple [ Type.RVar $ pack "b", Type.RVar $ pack "b" ]
                           , defLoc)
                  [ (pack "f", (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "b", defLoc))
                  , (pack "x", (Nothing, defLoc))
                  , (pack "y", (Nothing, defLoc))
                  ]
                  $ Expr.Tuple (Just $ Type.Tuple [ Type.RVar $ pack "b", Type.RVar $ pack "b" ], defLoc)
                  [ Expr.App (Just $ Type.RVar $ pack "b", defLoc)
                    (Expr.Var (Just $ Type.Fun [ Type.RVar $ pack "a" ] $ Type.RVar $ pack "b", defLoc)
                     $ pack "f"
                    )
                    [Expr.Var (Just $ Type.RVar $ pack "a", defLoc)
                     $ pack "x"
                    ]
                  , Expr.App (Just $ Type.RVar $ pack "b", defLoc)
                    (Expr.Var (Just $ Type.Fun [ Type.RVar $ pack "a" ] $ Type.RVar $ pack "b", defLoc)
                     $ pack "f"
                    )
                    [Expr.Var (Just $ Type.RVar $ pack "a", defLoc)
                     $ pack "x"
                    ]
                  ]
                 )
  , testCase "heterogenous instanciation" $
    let e = Expr.Abs (Nothing, defLoc) -- fun (f: a -> b) x y = (f x, f y)
          [ (pack "f", (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "b", defLoc))
            , (pack "x", (Just $ Type.RVar $ pack "a", defLoc))
            , (pack "y", (Just $ Type.RVar $ pack "a", defLoc))
            ]
            $ Expr.Tuple (Nothing, defLoc)
            [ Expr.App (Nothing, defLoc)
              (Expr.Var (Nothing, defLoc) $ pack "f")
              [Expr.Var (Nothing, defLoc) $ pack "x"]
            , Expr.App (Nothing, defLoc)
              (Expr.Var (Nothing, defLoc) $ pack "f")
              [Expr.Var (Nothing, defLoc) $ pack "x"]
            ]
        e' = Expr.Abs ( Just $ Type.Fun [ Type.Fun [ Type.RVar $ pack "a"] $ Type.RVar $ pack "b"
                                        , Type.RVar $ pack "a"
                                        , Type.RVar $ pack "a"
                                        ]
                        $ Type.Tuple [ Type.RVar $ pack "b", Type.RVar $ pack "b" ]
                      , defLoc)
             [ (pack "f", (Just $ Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "b", defLoc))
             , (pack "x", (Just $ Type.RVar $ pack "a", defLoc))
             , (pack "y", (Just $ Type.RVar $ pack "a", defLoc))
             ]
             $ Expr.Tuple (Just $ Type.Tuple [ Type.RVar $ pack "b", Type.RVar $ pack "b" ], defLoc)
             [ Expr.App (Just $ Type.RVar $ pack "b", defLoc)
               (Expr.Var (Just $ Type.Fun [ Type.RVar $ pack "a" ] $ Type.RVar $ pack "b", defLoc)
                 $ pack "f"
               )
               [Expr.Var (Just $ Type.RVar $ pack "a", defLoc)
                 $ pack "x"
               ]
             , Expr.App (Just $ Type.RVar $ pack "b", defLoc)
               (Expr.Var (Just $ Type.Fun [ Type.RVar $ pack "a" ] $ Type.RVar $ pack "b", defLoc)
                 $ pack "f"
               )
               [Expr.Var (Just $ Type.RVar $ pack "a", defLoc)
                 $ pack "x"
               ]
             ]
        f = Expr.App (Nothing, defLoc) e
            [ Expr.Var (Nothing, defLoc) $ pack "$id"
            , Expr.Literal (Nothing, defLoc) $ Literal.Integer 5
            , Expr.Literal (Nothing, defLoc) $ Literal.Character 'a'
            ]
    in evalStateT (runTC f) (initTC [] []) @?= Left (defLoc, UnifyFail Type.Integer Type.Character)
  ]
