module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Ann      (annz)
import qualified Ceu.Grammar.Exp  as E
import qualified Ceu.Grammar.Stmt as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

  describe "Env/Envs" $ do

      it "pass: 1st write" $
        envWrite [("x",Nothing)] "x" (Number 0) `shouldBe` [("x",Just (Number 0))]

      it "pass: 2nd write" $
        envWrite [("x",Just (Number 99))] "x" (Number 0) `shouldBe` [("x",Just (Number 0))]

      it "pass: write in middle" $
        envWrite [("a",Nothing),("x",Just (Number 99)),("b",Nothing)] "x" (Number 0) `shouldBe` [("a",Nothing),("x",Just (Number 0)),("b",Nothing)]

      it "pass: write in last" $
        envWrite [("a",Nothing),("b",Nothing),("x",Just (Number 99))] "x" (Number 0) `shouldBe` [("a",Nothing),("b",Nothing),("x",Just (Number 0))]

  describe "envRead vars id" $ do
      it "pass: read in simple env" $
        envRead [("x",Just (Number 0))] "x" `shouldBe` (Number 0)

      it "pass: read in complex env" $
        let vars = [("y",Just (Number 0)),("x",Just (Number 1)),("z",Just (Number 0))] in
          envRead vars "x" `shouldBe` (Number 1)

  describe "envEval vars exp" $ do
      it "pass: vars == [] && exp == (Number _)" $
        envEval [] (Number 0) `shouldBe` (Number 0)

      it "pass: eval in simple env" $
        let vars = [("x",Just (Number 1)),("y",Just (Number 2))] in
          envEval vars (Call "+" (Tuple [(Call "-" (Tuple [(Read "x"),(Number 3)])),(Call "negate" (Read "y"))]))
          `shouldBe` (Number (-4))

      it "pass: eval in complex env" $
        let vars = [("y",Just (Number 2)),("x",Just (Number 1)),("y",Just (Number 99)),("x",Just (Number 99))] in
          envEval vars (Call "+" (Tuple [(Call "-" (Tuple [(Read "x"),(Number 3)])),(Call "negate" (Read "y"))]))
          `shouldBe` (Number (-4))

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (Write "x" (Number 1)), [])
        `shouldBe` (Var ("x",(Just (Number 1))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Number 1))) (Write "x" (Number 2)), [])
        `shouldBe` (Var ("x",(Just (Number 2))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Write "x" (Number 1))), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Write "x" (Number 1)), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("x",(Just (Number 1)))
          (Var ("y",Nothing)
            (Write "y" (Call "+" (Tuple [(Read "x"),(Number 2)])))), []))
        `shouldBe` (Var ("x",(Just (Number 1))) (Var ("y",(Just (Number 3))) Nop), [])

      it "[x=1,y=?] y=x+2" $
        step
        (Var ("x",(Just (Number 1)))
        (Var ("y",Nothing)
          (Write "y" (Call "+" (Tuple [(Read "x"),(Number 2)])))), [])
        `shouldBe`
        (Var ("x",(Just (Number 1)))
        (Var ("y",(Just (Number 3))) Nop), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("x",(Just (Number 0)))
          (Write "x" (Call "negate" (Call "+" (Tuple [(Number 5),(Number 1)])))), [])
        `shouldBe`
        (Var ("x",(Just (Number (-6)))) Nop, [])

  describe "seq" $ do
      it "nop" $
        step (Seq Nop Nop, [])
        `shouldBe` (Nop, [])
      it "adv" $
        step (Seq (Seq Nop Nop) Nop, [])
        `shouldBe` (Seq Nop Nop, [])

  describe "if" $ do
      it "x == 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 0))])
        `shouldBe` (Nop, [("x",Just (Number 0))])
      it "x /= 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 1))])
        `shouldBe` (Nop, [("x",Just (Number 1))])

  describe "loop" $ do
      it "nop" $
        step (Loop' Nop Nop, [])
        `shouldBe` (Loop' Nop Nop, [])
{-
  describe "(Loop' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Escape 0) Nop, [])
        `shouldBe` (Escape 0, [])

      it "pass: lvl > 0" $
        step (Loop' (Escape 0) (Seq (EmitEvt "z") Nop), [])
        `shouldBe` ((Escape 0), [])
-}
      it "adv" $
        step (Loop' (Seq Nop Nop) Nop, [])
        `shouldBe` (Loop' Nop Nop, [])

  --------------------------------------------------------------------------
  describe "go" $ do

    evalProgItSuccess (Number 11)
      (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (E.Number annz 1) `G.sSeq`
            G.Ret   annz (E.Call annz "+" (E.Tuple annz [(E.Read annz "a"),(E.Number annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (Number 11)
      (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (E.Number annz 1) `G.sSeq`
            G.Var annz "b" (Type1 "Int") (G.Write annz (LVar "b") (E.Number annz 99)) `G.sSeq`
            G.Ret annz (E.Call annz "+" (E.Tuple annz [(E.Read annz "a"),(E.Number annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (Number 1)
      (G.Ret annz (E.Number annz 1) `G.sSeq`
          G.Var annz "_" (Type1 "Int") (G.Ret annz (E.Number annz 2)) `G.sSeq`
          G.Nop annz)

{-
    describe "typesystem:" $ do

        it "id(1)" $
            go
                (G.FuncI annz "id"
                    (TypeF (Type1 "Int") (Type1 "Int"))
                    (G.Var annz "_fret" (Type1 "Int")
                        (G.Write annz (LVar "_ret") (Read annz "_arg_0")))
                (G.Seq annz
                    (G.Write annz (LVar "_ret") (Call annz "id" (Number annz 1)))
                    (G.Escape annz 0)))
                []
            `shouldBe` Right (1,[[]])

        it "Int ; Bool ; Equalable a ; inst Equalable Bool/Int ; fff 1" $
            go
                (G.Data annz "Bool" [] [] False
                (G.Class annz "Equalable" ["a"]
                    (G.Func annz "fff" (TypeF (TypeV "a") (Type1 "Int")) (G.Nop annz))
                (G.Inst annz "Equalable" ["Bool"]
                    (G.Func annz "fff" (TypeF (Type1 "Bool") (Type1 "Int")) (G.Nop annz))
                (G.Inst annz "Equalable" ["Int"]
                    (G.Func annz "fff" (TypeF (Type1 "Int") (Type1 "Int")) (G.Nop annz))
                (G.Seq annz
                    (G.Write annz (LVar "_ret") (E.Call annz "fff" (E.Number annz 1)))
                    (G.Escape annz 0))))))
                []
            `shouldBe` Right (1,[[]])
-}

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (G.prelude annz p) `shouldBe` res))
