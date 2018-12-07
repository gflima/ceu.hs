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
      simplify' (Seq () (Escape () 0) (AwaitExt () "")) `shouldBe` (Escape () 0)

    it "Var () -> (Nop ())" $ do
      simplify' (Var () "" (Nop ())) `shouldBe` (Nop ())
    it "Var () -> Break" $ do
      simplify' (Var () "" (Escape () 0)) `shouldBe` (Escape () 0)
    it "Var () -> Break" $ do
      simplify' (Var () "" (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "Int () -> (Nop ())" $ do
      simplify' (Int () "" (Nop ())) `shouldBe` (Nop ())
    it "Int () -> Break" $ do
      simplify' (Int () "" (Escape () 0)) `shouldBe` (Escape () 0)
    it "Int () -> Break" $ do
      simplify' (Int () "" (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "If () a a -> a" $ do
      simplify' (If () (Const () 1) (AwaitExt () "") (AwaitExt () "")) `shouldBe` (AwaitExt () "")
    it "If () x y -> If () x y" $ do
      simplify' (If () (Const () 1) (Escape () 0) (Nop ())) `shouldBe` (If () (Const () 1) (Escape () 0) (Nop ()))

    it "Every () x y -> Every () x y" $ do
      simplify' (Every () "a" (Escape () 0)) `shouldBe` (Every () "a" (Escape () 0))

  describe "pars:" $ do
    --it "Par () (Nop ()) y -> y" $ do
      --simplify' (Par () (Nop ()) (Seq () (Escape () 0) (Nop ()))) `shouldBe` (Escape () 0)
    it "Par () x Break -> Break" $ do
      simplify' (Par () (Seq () (Escape () 0) (Nop ())) (AwaitExt () "")) `shouldBe` (Escape () 0)
    it "Par () x Break -> Break" $ do
      simplify' (Par () (Seq () (AwaitExt () "") (Nop ())) (AwaitExt () "")) `shouldBe` (Par () (AwaitExt () "") (AwaitExt () ""))

    --it "Par () (Nop ()) y -> y" $ do
      --simplify' (Par () (Nop ()) (Seq () (Escape () 0) (Nop ()))) `shouldBe` (Escape () 0)
    it "Par () Break x -> Break" $ do
      simplify' (Par () (Seq () (Escape () 0) (Nop ())) (AwaitExt () "")) `shouldBe` (Escape () 0)
    it "Par () x y -> Par () x y" $ do
      simplify' (Par () (Seq () (AwaitExt () "") (Nop ())) (AwaitExt () "")) `shouldBe` (Par () (AwaitExt () "") (AwaitExt () ""))
    it "par for par for par for" $ do
      simplify' (Par () (AwaitExt () "FOREVER") (Par () (AwaitExt () "FOREVER") (AwaitExt () "FOREVER")))
      `shouldBe` (AwaitExt () "FOREVER")
    it "nop or nop or nop" $ do
      simplify' (Trap () (Par () (Seq () (Nop ()) (Escape () 0)) (Seq () (Trap () (Par () (Seq () (Nop ()) (Escape () 0)) (AwaitExt () "FOREVER"))) (Escape () 0))))
      `shouldBe` (Nop ())
    it "nop and nop" $ do
      simplify' (Trap () (Var () "__and" (Seq () (Write () "__and" (Const () 0)) (Par () (Seq () (Nop ()) (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER")))) (Seq () (Nop ()) (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER"))))))))
      `shouldBe` (Nop ())
    it "nop and nop and nop" $ do
      simplify' (Trap () (Var () "__and" (Seq () (Write () "__and" (Const () 0)) (Par () (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER"))) (Seq () (Trap () (Var () "__and" (Seq () (Write () "__and" (Const () 0)) (Par () (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER"))) (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER"))))))) (If () (Equ () (Read () "__and") (Const () 1)) (Escape () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (AwaitExt () "FOREVER"))))))))
      `shouldBe` (Nop ())

    it "Pause () -> (Nop ())" $ do
      simplify' (Pause () "" (Nop ())) `shouldBe` (Nop ())
    it "Pause () -> Break" $ do
      simplify' (Pause () "" (Escape () 0)) `shouldBe` (Escape () 0)
    it "Pause () -> Break" $ do
      simplify' (Pause () "" (Seq () (Nop ()) (Escape () 0))) `shouldBe` (Escape () 0)

    it "Fin () -> (Nop ())" $ do
      simplify' (Fin () (Var () "" (Trap () (Escape () 0)))) `shouldBe` (Nop ())
    it "Fin () -> (Nop ())" $ do
      simplify' (Fin () (Var () "" (If () (Const () 1) (Nop ()) (Escape () 0)))) `shouldBe` (Fin () (Var () "" (If () (Const () 1) (Nop ()) (Escape () 0))))

    it "Trap () (Nop ()) -> (Nop ())" $ do
      simplify' (Trap () (Nop ())) `shouldBe` (Nop ())
    it "Trap () (Escape () 0) -> (Nop ())" $ do
      simplify' (Trap () (Escape () 0)) `shouldBe` (Nop ())
    it "Trap () (Escape () n) -> Escape () n" $ do
      simplify' (Trap () (Escape () 1)) `shouldBe` (Escape () 1)
    it "Trap () p -> Trap () p" $ do
      simplify' (Trap () (AwaitExt () "")) `shouldBe` (Trap () (AwaitExt () ""))
