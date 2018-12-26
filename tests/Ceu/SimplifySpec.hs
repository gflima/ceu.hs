module Ceu.SimplifySpec (main, spec) where

import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import Ceu.Grammar.Simplify
import Test.Hspec

main :: IO ()
main = hspec spec

simplify' :: Stmt () -> Stmt ()
simplify' p = simplify p

spec :: Spec
spec = do

  describe "simplify" $ do
    it "(Nop ()) -> (Nop ())" $ do
      simplify' (Nop ()) `shouldBe` (Nop ())
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Nop ()) (Nop ()))   `shouldBe` (Nop ())
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Nop ()) (Escape () 0)) `shouldBe` (Escape () 0)
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Escape () 0) (Nop ())) `shouldBe` (Escape () 0)
    it "Loop-Escape () -> (Nop ())" $ do
      simplify' (Loop () (Escape () 0))    `shouldBe` (Escape () 0)
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Seq () (Nop ()) (Escape () 0)) (Nop ())) `shouldBe` (Escape () 0)
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Nop ()) (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)
    it "Seq () -> (Nop ())" $ do
      simplify' (Seq () (Nop ()) (Seq () (Nop ()) (Trap () (Escape () 0)))) `shouldBe` (Nop ())
    it "Break;* -> Break" $ do
      simplify' (Seq () (Escape () 0) (AwaitInp () "")) `shouldBe` (Escape () 0)

    it "Var () -> (Nop ())" $ do
      simplify' (Var () "" [] (Nop ())) `shouldBe` (Nop ())
    it "Var () -> Break" $ do
      simplify' (Var () "" [] (Escape () 0)) `shouldBe` (Escape () 0)
    it "Var () -> Break" $ do
      simplify' (Var () "" [] (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "Evt () -> (Nop ())" $ do
      simplify' (Evt () "" (Nop ())) `shouldBe` (Nop ())
    it "Evt () -> Break" $ do
      simplify' (Evt () "" (Escape () 0)) `shouldBe` (Escape () 0)
    it "Evt () -> Break" $ do
      simplify' (Evt () "" (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "If () a a -> a" $ do
      simplify' (If () (Const () 1) (AwaitInp () "") (AwaitInp () "")) `shouldBe` (AwaitInp () "")
    it "If () x y -> If () x y" $ do
      simplify' (If () (Const () 1) (Escape () 0) (Nop ())) `shouldBe` (If () (Const () 1) (Escape () 0) (Nop ()))

    it "Every () x y -> Every () x y" $ do
      simplify' (Every () "a" (Escape () 0)) `shouldBe` (Every () "a" (Escape () 0))

  describe "pars:" $ do
    --it "Par () (Nop ()) y -> y" $ do
      --simplify' (Par () (Nop ()) (Seq () (Escape () 0) (Nop ()))) `shouldBe` (Escape () 0)
    it "Par () x Break -> Break" $ do
      simplify' (Par () (Seq () (Escape () 0) (Nop ())) (AwaitInp () "")) `shouldBe` (Escape () 0)
    it "Par () x Break -> Break" $ do
      simplify' (Par () (Seq () (AwaitInp () "") (Nop ())) (AwaitInp () "")) `shouldBe` (Par () (AwaitInp () "") (AwaitInp () ""))

    --it "Par () (Nop ()) y -> y" $ do
      --simplify' (Par () (Nop ()) (Seq () (Escape () 0) (Nop ()))) `shouldBe` (Escape () 0)
    it "Par () Break x -> Break" $ do
      simplify' (Par () (Seq () (Escape () 0) (Nop ())) (AwaitInp () "")) `shouldBe` (Escape () 0)
    it "Par () x y -> Par () x y" $ do
      simplify' (Par () (Seq () (AwaitInp () "") (Nop ())) (AwaitInp () "")) `shouldBe` (Par () (AwaitInp () "") (AwaitInp () ""))
    it "par for par for par for" $ do
      simplify' (Par () (Halt ()) (Par () (Halt ()) (Halt ())))
      `shouldBe` (Halt ())

    it "Pause () -> (Nop ())" $ do
      simplify' (Pause () "" (Nop ())) `shouldBe` (Nop ())
    it "Pause () -> Break" $ do
      simplify' (Pause () "" (Escape () 0)) `shouldBe` (Escape () 0)
    it "Pause () -> Break" $ do
      simplify' (Pause () "" (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "Fin () -> (Nop ())" $ do
      simplify' (Fin () (Var () "" [] (Trap () (Escape () 0)))) `shouldBe` (Nop ())
    it "Fin () -> (Nop ())" $ do
      simplify' (Fin () (Var () "" [] (If () (Const () 1) (Nop ()) (Escape () 0)))) `shouldBe` (Fin () (Var () "" [] (If () (Const () 1) (Nop ()) (Escape () 0))))

    it "Trap () (Nop ()) -> (Nop ())" $ do
      simplify' (Trap () (Nop ())) `shouldBe` (Nop ())
    it "Trap () (Escape () 0) -> (Nop ())" $ do
      simplify' (Trap () (Escape () 0)) `shouldBe` (Nop ())
    it "Trap () (Escape () n) -> Escape () n" $ do
      simplify' (Trap () (Escape () 1)) `shouldBe` (Escape () 1)
    it "Trap () p -> Trap () p" $ do
      simplify' (Trap () (AwaitInp () "")) `shouldBe` (Trap () (AwaitInp () ""))
