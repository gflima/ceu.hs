module Ceu.SimplifySpec (main, spec) where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Ann      (annz)
import Ceu.Grammar.Exp      (Exp(..))
import Ceu.Grammar.Stmt     (Stmt(..))
import Ceu.Grammar.Simplify
import Test.Hspec

main :: IO ()
main = hspec spec

simplify' :: Stmt -> Stmt
simplify' p = simplify p

spec :: Spec
spec = do

  describe "simplify" $ do
    it "(Nop annz) -> (Nop annz)" $ do
      simplify' (Nop annz) `shouldBe` (Nop annz)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Nop annz) (Nop annz))   `shouldBe` (Nop annz)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Nop annz) (Escape annz 0)) `shouldBe` (Escape annz 0)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Escape annz 0) (Nop annz)) `shouldBe` (Escape annz 0)
    it "Loop-Escape annz -> (Nop annz)" $ do
      simplify' (Loop annz (Escape annz 0))    `shouldBe` (Escape annz 0)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Seq annz (Nop annz) (Escape annz 0)) (Nop annz)) `shouldBe` (Escape annz 0)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Nop annz) (Seq annz (Nop annz) (Escape annz 0))) `shouldBe` (Escape annz 0)
    it "Seq annz -> (Nop annz)" $ do
      simplify' (Seq annz (Nop annz) (Seq annz (Nop annz) (Trap annz (Escape annz 0)))) `shouldBe` (Nop annz)
    it "Break;* -> Break" $ do
      simplify' (Seq annz (Escape annz 0) (AwaitInp annz "")) `shouldBe` (Escape annz 0)

    it "Var annz -> (Nop annz)" $ do
      simplify' (Var annz "" Type0 (Nop annz)) `shouldBe` (Nop annz)
    it "Var annz -> Break" $ do
      simplify' (Var annz "" Type0 (Escape annz 0)) `shouldBe` (Escape annz 0)
    it "Var annz -> Break" $ do
      simplify' (Var annz "" Type0 (Seq annz (Nop annz) (Escape annz 0))) `shouldBe` (Escape annz 0)

    it "Evt annz -> (Nop annz)" $ do
      simplify' (Evt annz "" (Nop annz)) `shouldBe` (Nop annz)
    it "Evt annz -> Break" $ do
      simplify' (Evt annz "" (Escape annz 0)) `shouldBe` (Escape annz 0)
    it "Evt annz -> Break" $ do
      simplify' (Evt annz "" (Seq annz (Nop annz) (Escape annz 0))) `shouldBe` (Escape annz 0)

    it "write unit" $ do
      simplify' (Write annz (LVar "") (Unit annz)) `shouldBe` (Nop annz)
    it "write unit" $ do
      simplify' (Seq annz (Write annz (LVar "") (Unit annz)) (Nop annz)) `shouldBe` (Nop annz)

    it "If annz a a -> a" $ do
      simplify' (If annz (Const annz 1) (AwaitInp annz "") (AwaitInp annz "")) `shouldBe` (AwaitInp annz "")
    it "If annz x y -> If annz x y" $ do
      simplify' (If annz (Const annz 1) (Escape annz 0) (Nop annz)) `shouldBe` (If annz (Const annz 1) (Escape annz 0) (Nop annz))

    it "Every annz x y -> Every annz x y" $ do
      simplify' (Every annz "a" (Escape annz 0)) `shouldBe` (Every annz "a" (Escape annz 0))

  describe "pars:" $ do
    --it "Par annz (Nop annz) y -> y" $ do
      --simplify' (Par annz (Nop annz) (Seq annz (Escape annz 0) (Nop annz))) `shouldBe` (Escape annz 0)
    it "Par annz x Break -> Break" $ do
      simplify' (Par annz (Seq annz (Escape annz 0) (Nop annz)) (AwaitInp annz "")) `shouldBe` (Escape annz 0)
    it "Par annz x Break -> Break" $ do
      simplify' (Par annz (Seq annz (AwaitInp annz "") (Nop annz)) (AwaitInp annz "")) `shouldBe` (Par annz (AwaitInp annz "") (AwaitInp annz ""))

    --it "Par annz (Nop annz) y -> y" $ do
      --simplify' (Par annz (Nop annz) (Seq annz (Escape annz 0) (Nop annz))) `shouldBe` (Escape annz 0)
    it "Par annz Break x -> Break" $ do
      simplify' (Par annz (Seq annz (Escape annz 0) (Nop annz)) (AwaitInp annz "")) `shouldBe` (Escape annz 0)
    it "Par annz x y -> Par annz x y" $ do
      simplify' (Par annz (Seq annz (AwaitInp annz "") (Nop annz)) (AwaitInp annz "")) `shouldBe` (Par annz (AwaitInp annz "") (AwaitInp annz ""))
    it "par for par for par for" $ do
      simplify' (Par annz (Halt annz) (Par annz (Halt annz) (Halt annz)))
      `shouldBe` (Halt annz)

    it "Pause annz -> (Nop annz)" $ do
      simplify' (Pause annz "" (Nop annz)) `shouldBe` (Nop annz)
    it "Pause annz -> Break" $ do
      simplify' (Pause annz "" (Escape annz 0)) `shouldBe` (Escape annz 0)
    it "Pause annz -> Break" $ do
      simplify' (Pause annz "" (Seq annz (Nop annz) (Escape annz 0))) `shouldBe` (Escape annz 0)

    it "Fin annz -> (Nop annz)" $ do
      simplify' (Fin annz (Var annz "" Type0 (Trap annz (Escape annz 0)))) `shouldBe` (Nop annz)
    it "Fin annz -> (Nop annz)" $ do
      simplify' (Fin annz (Var annz "" Type0 (If annz (Const annz 1) (Nop annz) (Escape annz 0)))) `shouldBe` (Fin annz (Var annz "" Type0 (If annz (Const annz 1) (Nop annz) (Escape annz 0))))

    it "Trap annz (Nop annz) -> (Nop annz)" $ do
      simplify' (Trap annz (Nop annz)) `shouldBe` (Nop annz)
    it "Trap annz (Escape annz 0) -> (Nop annz)" $ do
      simplify' (Trap annz (Escape annz 0)) `shouldBe` (Nop annz)
    it "Trap annz (Escape annz n) -> Escape annz n" $ do
      simplify' (Trap annz (Escape annz 1)) `shouldBe` (Escape annz 1)
    it "Trap annz p -> Trap annz p" $ do
      simplify' (Trap annz (AwaitInp annz "")) `shouldBe` (Trap annz (AwaitInp annz ""))
