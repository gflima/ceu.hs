module CeuSpec where

import Ceu
import Control.DeepSeq
import Control.Exception
import Test.Hspec

-- Declare Stmt as a datatype that can be fully evaluated.
-- This is required by some of the `shouldThrow` calls below.
instance NFData Stmt where
  rnf Nop = ()
  rnf (AwaitInt e) = ()
  rnf (Seq p q) = rnf p `seq` rnf q
  rnf (Loop' p q) = rnf p
  rnf (And' p q) = rnf p `seq` rnf q
  rnf (Or' p q) = rnf p `seq` rnf q

main :: IO ()
main = hspec $ do

  -- Env/Envs --------------------------------------------------------------
  describe "envsDcl envs id" $ do
    it "fail: envs == []" $
      evaluate (envsDcl [] "x")
      `shouldThrow` errorCall "envsDcl: bad environment"

    it "pass: 1st declaration" $
      envsDcl [newEnv] "x" `shouldBe` [(["x"],[])]

    it "pass: 2nd declaration, same env" $
      envsDcl [(["x"],[])] "y" `shouldBe` [(["y","x"],[])]

    it "pass: redeclaration, same env" $ -- CHECK THIS! --
      envsDcl [(["y","x"],[])] "x" `shouldBe` [(["x","y", "x"],[])]

    it "pass: redeclaration, inner env (shadowing)" $
      envsDcl (newEnv:[(["x"],[])]) "y" `shouldBe` [(["y"],[]),(["x"],[])]

  describe "envsGet envs id" $ do
    it "fail: envs == []" $
      evaluate (envsGet [] "x")
      `shouldThrow` errorCall "envsGet: bad environment"

    it "fail: undeclared variable" $
      evaluate (envsGet [newEnv] "x")
      `shouldThrow` errorCall "envsGet: undeclared variable"

    it "pass: finds in simple env" $
      envsGet [(["x"],[("x",0)])] "x" -- CHECK THIS! --
      `shouldBe` ([],(["x"],[("x",0)]),[])

    it "pass: finds in complex env" $
      let envs = [(["z"],[]),
                  (["y"],[("y",1)]),
                  (["y"],[("y",0)]),
                  (["x"],[])] in
        envsGet envs "y"
        `shouldBe` ([(["z"],[])],
                     (["y"],[("y",1)]),
                     [(["y"],[("y",0)]),(["x"],[])])

  -- nst1 ------------------------------------------------------------------
  describe "nst1" $ do

    -- block --
    describe "(Block p)" $ do
      it "transit: Block Nop" $
        nst1 (Block Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq Nop (Envs' 1), 0, Nothing, [newEnv,newEnv])

    -- envs' --
    describe "(Envs' envs)" $ do
      it "transit: [e1,e2] " $
        nst1 (Envs' 1, 0, Nothing, [newEnv,newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

    -- var --
    describe "(Var id)" $ do
      it "transit: x" $
        nst1 (Var "x", 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[])])

    -- write --
    describe "(Write id exp)" $ do
      it "error: x=y undef" $
        (evaluate . force) (nst1 (Write "x" (Read "y"), 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "error: x=1" $
        (evaluate . force) (nst1 (Write "x" (Const 1), 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "transit: [x=?] x=1" $
        nst1 (Write "x" (Const 1), 0, Nothing, [(["x"],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",1)])])

      it "transit: [x=1] x=2" $
        nst1 (Write "x" (Const 2), 0, Nothing, [(["x"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",2),("x",1)])])

      it "transit: nop;x=1" $
        nst1 (Seq Nop (Write "x" (Const 1)), 0, Nothing, [([],[])])
        `shouldBe` ((Write "x" (Const 1)), 0, Nothing, [([],[])])

      it "error: [x=1] y=x+2" $
        (evaluate . force) (nst1 (Write "y" (Read "x" `Add` Const 2), 0, Nothing, [(["x"],[("x",1)])]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "transit: [x=1,y=?] y=x+2" $
        nst1 (Write "y" (Add (Read "x") (Const 2)), 0, Nothing, [(["x","y"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x","y"],[("y",3),("x",1)])])

      it "transit: [x=?] x=-(5+1)" $
        nst1 (Write "x" (Umn (Add (Const 5) (Const 1))), 0, Nothing, [(["x"],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"], [("x",-6)])])

    -- emit-int --
    describe "(EmitInt e')" $ do
      it "transit: lvl == 0" $
        nst1 (EmitInt 0, 0, Nothing, [([],[])])
        `shouldBe` (CanRun 0, 0, Just 0, [([],[])])

      it "transit: lvl > 0" $
        nst1 (EmitInt 1, 3, Nothing, [([],[])])
        `shouldBe` (CanRun 3, 3, Just 1, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (EmitInt 1, 3, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- can-run --
    describe "(CanRun n)" $ do
      it "transit: n == lvl" $
        nst1 (CanRun 0, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: n == lvl" $
        nst1 (CanRun 8, 8, Nothing, [([],[])])
        `shouldBe` (Nop, 8, Nothing, [([],[])])

      it "error: n > lvl" $
        evaluate (nst1 (CanRun 8, 6, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "error: n < lvl" $
        evaluate (nst1 (CanRun 8, 12, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "error: evt /= nil" $
        evaluate (nst1 (CanRun 0, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-nop --
    describe "(Seq Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq Nop Nop, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Seq Nop Break, 3, Nothing, [([],[])])
        `shouldBe` (Break, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Seq Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-brk --
    describe "(Seq Break q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq Break Nop, 0, Nothing, [([],[])])
        `shouldBe` (Break, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Seq Break (EmitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (Break, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Seq Break Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-adv --
    describe "(Seq p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq (Seq Nop Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Seq (Seq (EmitInt 8) Nop) Nop, 3, Nothing, [([],[])])
        `shouldBe` (Seq (Seq (CanRun 3) Nop) Nop, 3, Just 8, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Seq (Seq Nop Nop) Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "error: isBlocked p" $
        (evaluate . force) (nst1 (Seq (Fin Nop) Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- if --
    describe "(If exp p q)" $ do
      it "error: x undef" $
        evaluate (nst1 (If (Read "x") Nop Break, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "transit: x == 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",0)])])
        `shouldBe` (Break, 0, Nothing, [(["x"],[("x",0)])])

      it "transit: x /= 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",1)])])

    -- loop-expd --
    describe "(Loop p)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop Nop, 0, Nothing, [([],[])])
        `shouldBe` (Seq (Loop' Nop Nop) (Envs' 1),0,Nothing,[([],[])])

      it "transit: lvl > 0" $
        nst1 (Loop (Seq Nop (EmitInt 8)), 3, Nothing, [([],[])])
        `shouldBe` (Seq (Loop' (Seq Nop (EmitInt 8)) (Seq Nop (EmitInt 8)))
                          (Envs' 1),3,Nothing,[([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Loop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p" $
        nst1 (Loop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Loop' (Fin Nop) (Fin Nop)) (Envs' 1),0,Nothing,[([],[])])

    -- loop-nop --
    describe "(Loop' Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' Nop Nop, 0, Nothing, [([],[])])
        `shouldBe` (Loop Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Loop' Nop (EmitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (Loop (EmitInt 8), 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Loop' Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $
        nst1 (Loop' Nop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Loop (Fin Nop), 0, Nothing, [([],[])])

    -- loop-brk --
    describe "(Loop' Break q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' Break Nop, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Loop' Break (Seq (EmitInt 8) Nop), 3, Nothing, [([],[])])
        `shouldBe` (Nop, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Loop' Break Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $
        nst1 (Loop' Break (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

    -- loop-adv --
    describe "(Loop' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' (Seq Nop Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Loop' Nop Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Loop' (Seq (EmitInt 8) Nop) Break, 3, Nothing, [([],[])])
        `shouldBe` (Loop' (Seq (CanRun 3) Nop) Break, 3, Just 8, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Loop' (Seq Nop Nop) Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "error: isBlocked p" $
        (evaluate . force) (nst1 (Loop' (Fin Nop) Nop, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: not (isBlocked p) && isBlocked q" $
        nst1 (Loop' (Seq Nop Nop) (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Loop' Nop (Fin Nop), 0, Nothing, [([],[])])

    -- and-expd --
    describe "(And p q)" $ do
      it "transit: lvl == 0" $
        nst1 (And Nop Nop, 0, Nothing, [([],[])])
        `shouldBe` (And' Nop (Seq (CanRun 0) Nop), 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (And (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, [([],[])])
        `shouldBe` (And' (Seq Nop (EmitInt 8))
                          (Seq (CanRun 3) (Seq Nop Nop)), 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p" $
        nst1 (And (Fin Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) Nop), 0, Nothing, [([],[])])

      it "transit: isBlocked q" $
        nst1 (And Nop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (And' Nop (Seq (CanRun 0) (Fin Nop)), 0, Nothing, [([],[])])

      it "transit: isBlocked p && isBlocked q" $
        nst1 (And (Fin Nop) (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (And' (Fin Nop)
                          (Seq (CanRun 0) (Fin Nop)), 0, Nothing, [([],[])])

    -- and-nop1 --
    describe "(And' Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (And' Nop Nop, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (And' Nop (EmitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (EmitInt 8, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And' Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $
        nst1 (And' Nop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Fin Nop, 0, Nothing, [([],[])])

      it "transit: q == Break" $
        nst1 (And' Nop Break, 0, Nothing, [([],[])])
        `shouldBe` (Break, 0, Nothing, [([],[])])

    -- and-brk1 --
    describe "(And' Break q)" $ do
      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (And' Break (AwaitExt 0), 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (And' Break (AwaitInt 0), 3, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And' Break (Var "x"), 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $ -- clear q == (Seq Nop Nop)
        nst1 (And' Break (Fin (Seq Nop Nop)), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop Nop) Break, 0, Nothing, [([],[])])

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (And' Break        -- clear q == Emit1; Emit2; Emit3
               (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4)))))), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop (Seq (EmitInt 1) (Seq (Seq (EmitInt 2) (EmitInt 3)) Nop))) Break,0,Nothing,[([],[])])

      it "transit: q == Break" $
        nst1 (And' Break (Seq (CanRun 1) Break), 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

    -- and-nop2 --
    describe "(And' p Nop)" $ do
      it "transit: lvl == 0 && isBlocked p" $
        nst1 (And' (Fin Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Fin Nop, 0, Nothing, [([],[])])

      it "transit: lvl >= 0 && isBlocked p" $
        nst1 (And' (Seq (Fin Nop) Nop) Nop, 3, Nothing, [([],[])])
        `shouldBe` (Seq (Fin Nop) Nop, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And' (Fin Nop) Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- and-brk2 --
    describe "(And' p Break)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (And' (AwaitInt 1) Break, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

      it "transit: lvl > 0 && isBlocked p" $ -- clear p == (Seq Nop Nop)
        nst1 (And' (Fin (Seq Nop Nop)) Break, 3, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop Nop) Break, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And' (Fin Nop) Break, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p && nontrivial clear" $
        nst1 (And' (Or' (Seq (AwaitInt 0) Nop)
                    (And' (Fin (EmitInt 1))
                     (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                      (Seq (AwaitInt 1) Nop))))
               Break, 0, Nothing, [([],[])]) -- clear q == Emit1; Emit2; Emit3
        `shouldBe` (Seq (Seq Nop (Seq (EmitInt 1) (Seq (Seq (EmitInt 2) (EmitInt 3)) Nop))) Break,0,Nothing,[([],[])])

      it "transit: p == Break" $ -- go-to: (And' Break q)
        nst1 (And' (AwaitExt 0) Break, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

    -- and-adv --
    describe "(And' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (And' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [([],[])])
        `shouldBe` (And' Nop (Seq Break Break), 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (And' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop), 3, Nothing, [([],[])])
        `shouldBe` (And' (Seq (CanRun 3) Nop)
                          (Seq (EmitInt 9) Nop), 3, Just 8, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (And' (Seq Nop Nop) (Seq Nop Nop), 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p" $
        nst1 (And' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, [([],[])])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, [([],[])])

      it "transit: isBlocked q" $
        nst1 (And' (EmitInt 8) (AwaitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (And' (CanRun 3) (AwaitInt 8), 3, Just 8, [([],[])])

      it "error: isBlocked p && isBlocked q" $
        (evaluate . force) (nst1 (And' (AwaitInt 3) (AwaitInt 4), 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- or-expd --
    describe "(Or p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Or Nop Nop, 0, Nothing, [([],[])])
        `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) Nop))
                          (Envs' 1),0,Nothing,[([],[])])

      it "transit: lvl > 0" $
        nst1 (Or (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, [([],[])])
        `shouldBe` (Seq (Or' (Seq Nop (EmitInt 8)) (Seq (CanRun 3)
                          (Seq Nop Nop))) (Envs' 1),3,Nothing,[([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Or Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p" $
        nst1 (Or (Fin Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) Nop))
                          (Envs' 1),0,Nothing,[([],[])])

      it "transit: isBlocked q" $
        nst1 (Or Nop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) (Fin Nop)))
                          (Envs' 1),0,Nothing,[([],[])])

      it "transit: isBlocked p && isBlocked q" $
        nst1 (Or (Fin Nop) (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)))
                          (Envs' 1),0,Nothing,[([],[])])

    -- or-nop1 --
    describe "(Or' Nop q)" $ do
      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (Or' Nop (AwaitInt 0), 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (Or' Nop (AwaitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (Nop, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Or' Nop Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $ -- clear q == Nop
        nst1 (Or' Nop (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (Or' Nop           -- clear q == Emit1; Emit2; Emit3
               (And' (Seq (AwaitInt 0) (Fin Nop))
                 (Or' (Fin (EmitInt 1))
                  (And' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 1) (Fin (EmitInt 4)))))), 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop (Seq (EmitInt 1) (Seq (Seq (EmitInt 2) (EmitInt 3)) Nop)),0,Nothing,[([],[])])

      it "error: q == Break" $ -- clear q == Nop -- CHECK THIS! --
        (evaluate . force) (nst1 (Or' Nop Break, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "transit: q == Break" $ -- clear q == Nop -- CHECK THIS! --
        nst1 (Or' (AwaitInt 0) Break, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

    -- or-brk1 --
    describe "(Or' Break q)" $ do
      it "error: lvl == 0" $  -- clear q == Nop
        (evaluate . force) (nst1 (Or' Break Nop, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (Or' Break (AwaitInt 0), 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (Or' Break (AwaitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 3, Nothing, [([],[])])

      it "nothing: evt /= nil" $
        evaluate (nst1 (Or' Break Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked q" $ -- clear q == (Seq Nop Nop)
        nst1 (Or' Break (Fin (Seq Nop Nop)), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop Nop) Break, 0, Nothing, [([],[])])

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (Or' Break         -- clear q == Emit1; Emit2; Emit3
               (Or' (Seq (AwaitInt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4)))))), 0, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop (Seq (EmitInt 1) (Seq (Seq (EmitInt 2) (EmitInt 3)) Nop))) Break,0,Nothing,[([],[])])

      it "error: q == Break" $
        (evaluate . force) (nst1 (Or' Break Break, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "transit: q == Break" $
        nst1 (Or' Break (Seq (CanRun 1) Break), 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

    -- or-nop2 --
    describe "(Or' p Nop)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (Fin Nop) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "transit: lvl >= 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (Seq (Fin Nop) Nop) Nop, 3, Nothing, [([],[])])
        `shouldBe` (Nop, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Or' (Fin Nop) Nop, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- or-brk2 --
    describe "(Or' p Break)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (AwaitInt 1) Break, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

      it "transit: lvl > 0 && isBlocked p" $ -- clear p == (Seq Nop Nop)
        nst1 (Or' (Fin (Seq Nop Nop)) Break, 3, Nothing, [([],[])])
        `shouldBe` (Seq (Seq Nop Nop) Break, 3, Nothing, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Or' (Fin Nop) Break, 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p && nontrivial clear" $
        nst1 (Or' (Or' (Seq (AwaitInt 0) Nop)
                    (And' (Fin (EmitInt 1))
                     (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                      (Seq (AwaitInt 1) Nop))))
               Break, 0, Nothing, [([],[])]) -- clear q == Emit1; Emit2; Emit3
        `shouldBe` (Seq (Seq Nop (Seq (EmitInt 1) (Seq (Seq (EmitInt 2) (EmitInt 3)) Nop))) Break,0,Nothing,[([],[])])

      it "transit: p == Break" $ -- go-to: (Or' Break q)
        nst1 (Or' (AwaitExt 0) Break, 0, Nothing, [([],[])])
        `shouldBe` (Seq Nop Break, 0, Nothing, [([],[])])

    -- or-adv --
    describe "(Or' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Or' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [([],[])])
        `shouldBe` (Or' Nop (Seq Break Break), 0, Nothing, [([],[])])

      it "transit: lvl > 0" $
        nst1 (Or' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop), 3, Nothing, [([],[])])
        `shouldBe` (Or' (Seq (CanRun 3) Nop)
                          (Seq (EmitInt 9) Nop), 3, Just 8, [([],[])])

      it "error: evt /= nil" $
        evaluate (nst1 (Or' (Seq Nop Nop) (Seq Nop Nop), 0, Just 1, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "transit: isBlocked p" $
        nst1 (Or' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, [([],[])])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, [([],[])])

      it "transit: isBlocked q" $
        nst1 (Or' (EmitInt 8) (AwaitInt 8), 3, Nothing, [([],[])])
        `shouldBe` (Or' (CanRun 3) (AwaitInt 8), 3, Just 8, [([],[])])

      it "error: isBlocked p && isBlocked q" $
        (evaluate . force) (nst1 (Or' (AwaitInt 3) (AwaitInt 4), 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- nsts -------------------------------------------------------------------
  describe "nsts" $ do
    describe "Zero steps: Program is blocked" $ do
      it "AwaitExt -> AwaitExt#" $
        nsts (AwaitExt 0, 0, Nothing, [([],[])])
        `shouldBe` (AwaitExt 0, 0, Nothing, [([],[])])

      it "AwaitInt -> AwaitInt#" $
        nsts (AwaitInt 0, 0, Nothing, [([],[])])
        `shouldBe` (AwaitInt 0, 0, Nothing, [([],[])])

      it "Seq -> Seq#" $
        nsts (Seq (AwaitInt 0) Nop, 0, Nothing, [([],[])])
        `shouldBe` (Seq (AwaitInt 0) Nop, 0, Nothing, [([],[])])

      it "Every -> Every#" $
        nsts (Every 0 Nop, 0, Nothing, [([],[])])
        `shouldBe` (Every 0 Nop, 0, Nothing, [([],[])])

      it "Fin -> Fin#" $
        nsts (Fin (Seq Nop Nop), 0, Nothing, [([],[])])
        `shouldBe` (Fin (Seq Nop Nop), 0, Nothing, [([],[])])

      it "And' -> And'#" $
        nsts (And' (AwaitExt 0) (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (And' (AwaitExt 0) (Fin Nop), 0, Nothing, [([],[])])

      it "Or' -> Or'#" $
        nsts (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, [([],[])])
        `shouldBe` (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, [([],[])])

      it "CanRun -> CanRun#" $
        evaluate (nsts (CanRun 5, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    describe "Zero steps: No nst-rule applies" $ do
      it "Nop -> Nop#" $
        nsts (Nop, 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [([],[])])

      it "Break -> Break#" $
        nsts (Break, 0, Nothing, [([],[])])
        `shouldBe` (Break, 0, Nothing, [([],[])])

    describe "One+ steps" $ do
      it "EmitInt -> CanRun#" $
        let d = (EmitInt 8, 3, Nothing, [([],[])])
            d' = (CanRun 3, 3, Just 8, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "CanRun -> Nop#" $
        let d = (CanRun 3, 3, Nothing, [([],[])])
            d' = (Nop, 3, Nothing, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Nop; Nop; Nop; Break; Nop -> Break#" $
        let p = Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop
            d = (p, 0, Nothing, [([],[])])
            d' = (Break, 0, Nothing, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Loop Break; Nop; Nop; EmitInt; Break -> CanRun#; Break" $
        let p = Loop Break `Seq` Nop `Seq` Nop `Seq` EmitInt 8 `Seq` Break
            d = (p, 3, Nothing, [([],[])])
            d' = (Seq (CanRun 3) Break, 3, Just 8, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "(Loop Break; Nop) && (EmitInt; Nop) -> CanRun#; Nop" $
        let p = Seq (Loop Break) Nop `And` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, [([],[])])
            d' = (Seq (CanRun 3) Nop, 3, Just 8, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "(Loop Break; Nop) || (EmitInt; Nop) -> Nop#" $
        let p = Seq (Loop Break) Nop `Or` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, [([],[])])
            d' = (Nop, 3, Nothing, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Loop ((Nop; AwaitInt) && (AwaitExt || Nop; Break)) -> Nop#" $
        let p = Loop ((Nop `Seq` AwaitInt 3)
                      `And` (AwaitExt 18 `Or` (Nop `Seq` Break)))
            d = (p, 0, Nothing, [([],[])])
            d' = (Nop, 0, Nothing, [([],[])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

  -- out1 ------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "transit: lvl == 0" $
        out1 (Nop, 0, Just 1, [([],[])])
        `shouldBe` (Nop, 1, Nothing, [([],[])])

      it "transit: lvl > 0" $
        out1 (Seq (AwaitInt 1) Break, 3, Just 1, [([],[])])
        `shouldBe` (Seq Nop Break, 4, Nothing, [([],[])])

      it "transit: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt 2) Break, 3, Just 1, [([],[])])
        `shouldBe` (Seq (AwaitInt 2) Break, 4, Nothing, [([],[])])

    -- pop --
    describe "pop" $ do
      it "nothing: lvl == 0" $
        evaluate (out1 (Nop, 0, Nothing, [([],[])]))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "transit: lvl > 0 && nst-irreducible" $
        out1 (Nop, 33, Nothing, [([],[])])
        `shouldBe` (Nop, 32, Nothing, [([],[])])

      it "nothing: lvl > 0 && not nst-irreducible" $
        evaluate (out1 (Seq Nop Nop, 1, Nothing, [([],[])]))
        `shouldThrow` errorCall "outPop: cannot advance"

  -- nsts_out1_s -------------------------------------------------------------------
  describe "nsts_out1_s" $ do
    describe "Zero steps: No out-rule applies" $ do
      it "lvl == 0" $
        let d = (Nop, 0, Nothing, [([],[])]) in
          (nsts_out1_s d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "not (isNstIrreducible p)" $
        let d = (Seq Nop Nop, 0, Nothing, [([],[])]) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` False)

    describe "One+ steps: One+ pops" $ do
      it "lvl > 0" $
        nsts_out1_s (Nop, 13, Nothing, [([],[])])
        `shouldBe`  (Nop, 0, Nothing, [([],[])])

    describe "One+ steps: One push followed by one+ pops" $ do
      it "lvl == 0" $
        nsts_out1_s (AwaitInt 3, 0, Just 3, [([],[])])
        `shouldBe`  (AwaitInt 3, 0, Just 3, [([],[])])

      it "lvl > 0" $
        nsts_out1_s (AwaitInt 3, 88, Just 3, [([],[])])
        `shouldBe`  (Nop, 0, Nothing, [([],[])])

  -- reaction -----------------------------------------------------------------
  describe "reaction" $ do

    it "Nop; (AwaitInt 3) && Nop; Fin Nop -> Nop" $
      reaction ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` Fin Nop), 3, [([],[])])
      `shouldBe` (AwaitInt 3 `And'` Fin Nop, [([],[])])

    it "Nop; (AwaitInt 3) && Nop; (EmitInt 3) -> Nop" $
      reaction ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` EmitInt 3), 1, [([],[])])
      `shouldBe` (Nop, [([],[])])

  -- evalProg -----------------------------------------------------------------
  describe "evalProg" $ do

    it "var a; var ret; a=1; ret=a+10;" $
      let p = Seq (Var "a") (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10))))) in
        (evalProg p) `shouldBe` 11

    it "var a; {var ret; a=1; ret=a+10;}" $
      let p = Seq (Var "a") (Block (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        evaluate (evalProg p)
        `shouldThrow` errorCall "envsGet: undeclared variable"

    it "var ret; ret=1; {var ret; ret=99;}" $
      let p = Seq (Var "ret") (Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Seq (Var "ret") (Write "ret" (Const 99)))))) in
        (evalProg p) `shouldBe` 1

    it "var ret; var a; a=1; {var a; a=99;} ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Block (Seq (Var "a") (Write "a" (Const 99)))) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p) `shouldBe` 11

    it "var ret; ret=1; {ret=2;}" $
      let p = Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Write "ret" (Const 2)))) in
        (evalProg p) `shouldBe` 2

    it "var ret; var a; a=1; ({var a; a=99; awaitExt E} || nop); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Or (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Nop) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p) `shouldBe` 11

    it "var ret; ({ret=1; awaitExt E} || nop);" $
      let p = Seq (Var "ret") (Or (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Nop) in
        (evalProg p) `shouldBe` 1

    it "var ret; var a; a=1; loop ({var a; a=99; awaitExt E} && break); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Loop (And (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Break)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p) `shouldBe` 11

    it "var ret; loop ({ret=1; awaitExt E} && break);" $
      let p = Seq (Var "ret") (Loop (And (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Break))in
        (evalProg p) `shouldBe` 1
