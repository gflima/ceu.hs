module Ceu.FullGrammarSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace

import Ceu.Grammar.Globals  (Loc(..))
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Ann      (Ann(type_),annz)

import qualified Ceu.Grammar.Basic as B
import qualified Ceu.Eval as E

import Ceu.Grammar.Full.Stmt
import Ceu.Grammar.Full.Eval
import qualified Ceu.Grammar.Full.Compile.Scope as Scope

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --describe "TODO" $ do
  --------------------------------------------------------------------------

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var annz "x" Type0)
        `shouldBe` ([], (Var' annz "x" Type0 (Nop annz)))

      it "var x; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" Type0) (Nop annz))
        `shouldBe` ([], (Var' annz "x" Type0 (Nop annz)))

      it "var x <- 1 ; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (Type1 "Int")) (Seq annz (Write annz (LVar "x") (B.Number annz 1)) (Nop annz)))
        `shouldBe` ([], (Var' annz "x" (Type1 "Int") (Seq annz (Write annz (LVar "x") (B.Number annz 1)) (Nop annz))))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var annz "x" Type0)) (Var annz "y" Type0))
        `shouldBe` ([],Seq annz (Var' annz "x" Type0 (Nop annz)) (Var' annz "y" Type0 (Nop annz)))

      it "scope var x end ; x=1" $ do
        compile' (Seq annz (Scope annz (Var annz "x" (Type1 "Int"))) (Write annz (LVar "x") (B.Number annz 1)))
        `shouldBe` (["type 'Int' is not declared","variable 'x' is not declared"], B.Seq annz (B.Var annz "x" (Type1 "Int") (B.Nop annz)) (B.Write annz (LVar "x") (B.Number (annz{type_=Type1 "Int"}) 1)))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (Var' annz "x" Type0 (Nop annz))
      `shouldBe` ([], (B.Var annz "x" Type0 (B.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (Var' annz "x" (Type1 "Int") (Write annz (LVar "x") (B.Number annz 1)))
      `shouldBe` (["type 'Int' is not declared"], (B.Var annz "x" (Type1 "Int") (B.Write annz (LVar "x") (B.Number annz{type_=Type1 "Int"} 1))))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (Ret annz (B.Number annz 1))
      `shouldBe` Right (E.Number 1)
