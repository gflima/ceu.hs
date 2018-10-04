module CeuSpec where

import Test.Hspec
import Ceu

newMEnvs = ([newEnv],[newEnv],[newEnv])

main :: IO ()
main = hspec $ do
  -- nst1 ------------------------------------------------------------------
  describe "nst1" $ do

    -- block --
    describe "(Block p)" $ do
      it "transit: Block Nop" $
        nst1 (Block Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop (MEnvs' 1), 0, Nothing, ([newEnv,newEnv],[newEnv,newEnv],[newEnv,newEnv]))

    -- envs' --
    describe "(MEnvs' envs)" $ do
      it "transit: [e1,e2] " $
        nst1 (MEnvs' 1, 0, Nothing, ([newEnv,newEnv],[newEnv,newEnv],[newEnv,newEnv]))
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

    -- var --
    describe "(Var id)" $ do
      it "transit: x" $
        nst1 (Var "x", 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x"],[])]))

    -- write --
    describe "(Write id exp)" $ do
      it "nothing: x=y undef" $
        nst1 (Write "x" (Read "y"), 0, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "nothing: x=1" $
        nst1 (Write "x" (Const 1), 0, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "transit: [x=?] x=1" $
        nst1 (Write "x" (Const 1), 0, Nothing, ([newEnv],[newEnv],[(["x"],[])]))
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",1)])]))

      it "transit: [x=1] x=2" $
        nst1 (Write "x" (Const 2), 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",1)])]))
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",2),("x",1)])]))

      it "transit: nop;x=1" $
        nst1 (Seq Nop (Write "x" (Const 1)), 0, Nothing, newMEnvs)
        `shouldBe` Just ((Write "x" (Const 1)), 0, Nothing, newMEnvs)

      it "nothing: [x=1] y=x+2" $
        nst1 (Write "y" (Add (Read "x") (Const 2)), 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",1)])]))
        `shouldBe` Nothing

      it "transit: [x=1,y=?] y=x+2" $
        nst1 (Write "y" (Add (Read "x") (Const 2)), 0, Nothing, ([newEnv],[newEnv],[(["x","y"],[("x",1)])]))
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x","y"],[("y",3),("x",1)])]))

      it "transit: [x=?] x=-(5+1)" $
        nst1 (Write "x" (Umn (Add (Const 5) (Const 1))), 0, Nothing, ([newEnv],[newEnv],[(["x"],[])]))
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x"], [("x",-6)])]))

    -- emit-int --
    describe "(EmitInt e')" $ do
      it "transit: lvl == 0" $
        nst1 (EmitInt 0, 0, Nothing, newMEnvs)
        `shouldBe` Just (CanRun 0, 0, Just 0, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (EmitInt 1, 3, Nothing, newMEnvs)
        `shouldBe` Just (CanRun 3, 3, Just 1, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (EmitInt 1, 3, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- can-run --
    describe "(CanRun n)" $ do
      it "transit: n == lvl" $
        nst1 (CanRun 0, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: n == lvl" $
        nst1 (CanRun 8, 8, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 8, Nothing, newMEnvs)

      it "nothing: n > lvl" $
        nst1 (CanRun 8, 6, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "nothing: n < lvl" $
        nst1 (CanRun 8, 12, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "nothing: evt /= nil" $
        nst1 (CanRun 0, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- seq-nop --
    describe "(Seq Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Seq Nop Break, 3, Nothing, newMEnvs)
        `shouldBe` Just (Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Seq Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- seq-brk --
    describe "(Seq Break q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq Break Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Break, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Seq Break (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Seq Break Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- seq-adv --
    describe "(Seq p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Seq (Seq Nop Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Seq (Seq (EmitInt 8) Nop) Nop, 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq (CanRun 3) Nop) Nop, 3, Just 8, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Seq (Seq Nop Nop) Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "nothing: isBlocked p" $
        nst1 (Seq (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Nothing

    -- if --
    describe "(If exp p q)" $ do
      it "nothing: x undef" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "transit: x == 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",0)])]))
        `shouldBe` Just (Break, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",0)])]))

      it "transit: x /= 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",1)])]))
        `shouldBe` Just (Nop, 0, Nothing, ([newEnv],[newEnv],[(["x"],[("x",1)])]))

    -- loop-expd --
    describe "(Loop p)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Loop' Nop Nop) (MEnvs' 1),0,Nothing,newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Loop (Seq Nop (EmitInt 8)), 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Loop' (Seq Nop (EmitInt 8)) (Seq Nop (EmitInt 8)))
                          (MEnvs' 1),3,Nothing,newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Loop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p" $
        nst1 (Loop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Loop' (Fin Nop) (Fin Nop)) (MEnvs' 1),0,Nothing,newMEnvs)

    -- loop-nop --
    describe "(Loop' Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Loop Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Loop' Nop (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Loop (EmitInt 8), 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Loop' Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $
        nst1 (Loop' Nop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Loop (Fin Nop), 0, Nothing, newMEnvs)

    -- loop-brk --
    describe "(Loop' Break q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' Break Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Loop' Break (Seq (EmitInt 8) Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Loop' Break Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $
        nst1 (Loop' Break (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

    -- loop-adv --
    describe "(Loop' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Loop' (Seq Nop Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Loop' Nop Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Loop' (Seq (EmitInt 8) Nop) Break, 3, Nothing, newMEnvs)
        `shouldBe` Just (Loop' (Seq (CanRun 3) Nop) Break, 3, Just 8, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Loop' (Seq Nop Nop) Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "nothing: isBlocked p" $
        nst1 (Loop' (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "transit: not (isBlocked p) && isBlocked q" $
        nst1 (Loop' (Seq Nop Nop) (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Loop' Nop (Fin Nop), 0, Nothing, newMEnvs)

    -- and-expd --
    describe "(And p q)" $ do
      it "transit: lvl == 0" $
        nst1 (And Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (And' Nop (Seq (CanRun 0) Nop), 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (And (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (And' (Seq Nop (EmitInt 8))
                          (Seq (CanRun 3) (Seq Nop Nop)), 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p" $
        nst1 (And (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (And' (Fin Nop) (Seq (CanRun 0) Nop), 0, Nothing, newMEnvs)

      it "transit: isBlocked q" $
        nst1 (And Nop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (And' Nop (Seq (CanRun 0) (Fin Nop)), 0, Nothing, newMEnvs)

      it "transit: isBlocked p && isBlocked q" $
        nst1 (And (Fin Nop) (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (And' (Fin Nop)
                          (Seq (CanRun 0) (Fin Nop)), 0, Nothing, newMEnvs)

    -- and-nop1 --
    describe "(And' Nop q)" $ do
      it "transit: lvl == 0" $
        nst1 (And' Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (And' Nop (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (EmitInt 8, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And' Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $
        nst1 (And' Nop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Fin Nop, 0, Nothing, newMEnvs)

      it "transit: q == Break" $
        nst1 (And' Nop Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Break, 0, Nothing, newMEnvs)

    -- and-brk1 --
    describe "(And' Break q)" $ do
      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (And' Break Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (And' Break (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And' Break Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $ -- clear q == (Seq Nop Nop)
        nst1 (And' Break (Fin (Seq Nop Nop)), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq Nop Nop) Break, 0, Nothing, newMEnvs)

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (And' Break        -- clear q == Emit1; Emit2; Emit3
               (Or' (Seq Nop (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq Nop (Fin (EmitInt 4)))))), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq (EmitInt 1) (Seq (EmitInt 2) (EmitInt 3)))
                          Break, 0, Nothing, newMEnvs)

      it "transit: q == Break" $
        nst1 (And' Break Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

    -- and-nop2 --
    describe "(And' p Nop)" $ do
      it "transit: lvl == 0 && isBlocked p" $
        nst1 (And' (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Fin Nop, 0, Nothing, newMEnvs)

      it "transit: lvl >= 0 && isBlocked p" $
        nst1 (And' (Seq (Fin Nop) Nop) Nop, 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Fin Nop) Nop, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And' (Fin Nop) Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- and-brk2 --
    describe "(And' p Break)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (And' (AwaitInt 1) Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

      it "transit: lvl > 0 && isBlocked p" $ -- clear p == (Seq Nop Nop)
        nst1 (And' (Fin (Seq Nop Nop)) Break, 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq Nop Nop) Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And' (Fin Nop) Break, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p && nontrivial clear" $
        nst1 (And' (Or' (Seq (AwaitInt 0) Nop)
                    (And' (Fin (EmitInt 1))
                     (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                      (Seq (AwaitInt 1) Nop))))
               Break, 0, Nothing, newMEnvs) -- clear q == Emit1; Emit2; Emit3
        `shouldBe` Just (Seq (Seq (EmitInt 1) (Seq (EmitInt 2) (EmitInt 3)))
                          Break, 0, Nothing, newMEnvs)

      it "transit: p == Break" $ -- go-to: (And' Break q)
        nst1 (And' Break Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

    -- and-adv --
    describe "(And' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (And' (Seq Nop Nop) (Seq Break Break), 0, Nothing, newMEnvs)
        `shouldBe` Just (And' Nop (Seq Break Break), 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (And' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (And' (Seq (CanRun 3) Nop)
                          (Seq (EmitInt 9) Nop), 3, Just 8, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (And' (Seq Nop Nop) (Seq Nop Nop), 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p" $
        nst1 (And' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (And' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, newMEnvs)

      it "transit: isBlocked q" $
        nst1 (And' (EmitInt 8) (AwaitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (And' (CanRun 3) (AwaitInt 8), 3, Just 8, newMEnvs)

      it "nothing: isBlocked p && isBlocked q" $
        nst1 (And' (AwaitInt 3) (AwaitInt 4), 0, Nothing, newMEnvs)
        `shouldBe` Nothing

    -- or-expd --
    describe "(Or p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Or Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Or' Nop (Seq (CanRun 0) Nop))
                          (MEnvs' 1),0,Nothing,newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Or (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Or' (Seq Nop (EmitInt 8)) (Seq (CanRun 3)
                          (Seq Nop Nop))) (MEnvs' 1),3,Nothing,newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p" $
        nst1 (Or (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Or' (Fin Nop) (Seq (CanRun 0) Nop))
                          (MEnvs' 1),0,Nothing,newMEnvs)

      it "transit: isBlocked q" $
        nst1 (Or Nop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Or' Nop (Seq (CanRun 0) (Fin Nop)))
                          (MEnvs' 1),0,Nothing,newMEnvs)

      it "transit: isBlocked p && isBlocked q" $
        nst1 (Or (Fin Nop) (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)))
                          (MEnvs' 1),0,Nothing,newMEnvs)

    -- or-nop1 --
    describe "(Or' Nop q)" $ do
      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (Or' Nop Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (Or' Nop (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or' Nop Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $ -- clear q == Nop
        nst1 (Or' Nop (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (Or' Nop           -- clear q == Emit1; Emit2; Emit3
               (And' (Seq Nop (Fin Nop))
                 (Or' (Fin (EmitInt 1))
                  (And' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq Nop (Fin (EmitInt 4)))))), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (EmitInt 1) (Seq (EmitInt 2) (EmitInt 3)),
                          0, Nothing, newMEnvs)

      -- *** CHECK THIS *** --
      it "transit: q == Break" $ -- clear q == Nop -- CHECK THIS! --
        nst1 (Or' Nop Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

    -- or-brk1 --
    describe "(Or' Break q)" $ do
      it "transit: lvl == 0" $  -- clear q == Nop
        nst1 (Or' Break Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $   -- clear q == Nop
        nst1 (Or' Break (EmitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or' Break Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked q" $ -- clear q == (Seq Nop Nop)
        nst1 (Or' Break (Fin (Seq Nop Nop)), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq Nop Nop) Break, 0, Nothing, newMEnvs)

      it "transit: isBlocked q && nontrivial clear" $
        nst1 (Or' Break         -- clear q == Emit1; Emit2; Emit3
               (Or' (Seq Nop (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq Nop (Fin (EmitInt 4)))))), 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq (EmitInt 1) (Seq (EmitInt 2) (EmitInt 3)))
                          Break, 0, Nothing, newMEnvs)

      it "transit: q == Break" $
        nst1 (Or' Break Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

    -- or-nop2 --
    describe "(Or' p Nop)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (Fin Nop) Nop, 0, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 0, Nothing, newMEnvs)

      it "transit: lvl >= 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (Seq (Fin Nop) Nop) Nop, 3, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or' (Fin Nop) Nop, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

    -- or-brk2 --
    describe "(Or' p Break)" $ do
      it "transit: lvl == 0 && isBlocked p" $ -- clear p == Nop
        nst1 (Or' (AwaitInt 1) Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

      it "transit: lvl > 0 && isBlocked p" $ -- clear p == (Seq Nop Nop)
        nst1 (Or' (Fin (Seq Nop Nop)) Break, 3, Nothing, newMEnvs)
        `shouldBe` Just (Seq (Seq Nop Nop) Break, 3, Nothing, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or' (Fin Nop) Break, 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p && nontrivial clear" $
        nst1 (Or' (Or' (Seq (AwaitInt 0) Nop)
                    (And' (Fin (EmitInt 1))
                     (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                      (Seq (AwaitInt 1) Nop))))
               Break, 0, Nothing, newMEnvs) -- clear q == Emit1; Emit2; Emit3
        `shouldBe` Just (Seq (Seq (EmitInt 1) (Seq (EmitInt 2) (EmitInt 3)))
                          Break, 0, Nothing, newMEnvs)

      it "transit: p == Break" $ -- go-to: (Or' Break q)
        nst1 (Or' Break Break, 0, Nothing, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 0, Nothing, newMEnvs)

    -- or-adv --
    describe "(Or' p q)" $ do
      it "transit: lvl == 0" $
        nst1 (Or' (Seq Nop Nop) (Seq Break Break), 0, Nothing, newMEnvs)
        `shouldBe` Just (Or' Nop (Seq Break Break), 0, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        nst1 (Or' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (Or' (Seq (CanRun 3) Nop)
                          (Seq (EmitInt 9) Nop), 3, Just 8, newMEnvs)

      it "nothing: evt /= nil" $
        nst1 (Or' (Seq Nop Nop) (Seq Nop Nop), 0, Just 1, newMEnvs)
        `shouldBe` Nothing

      it "transit: isBlocked p" $
        nst1 (Or' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, newMEnvs)
        `shouldBe` Just (Or' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, newMEnvs)

      it "transit: isBlocked q" $
        nst1 (Or' (EmitInt 8) (AwaitInt 8), 3, Nothing, newMEnvs)
        `shouldBe` Just (Or' (CanRun 3) (AwaitInt 8), 3, Just 8, newMEnvs)

      it "nothing: isBlocked p && isBlocked q" $
        nst1 (Or' (AwaitInt 3) (AwaitInt 4), 0, Nothing, newMEnvs)
        `shouldBe` Nothing

  -- nst -------------------------------------------------------------------
  describe "nst" $ do
    describe "Zero steps: Program is blocked" $ do
      it "AwaitExt -> AwaitExt#" $
        nst (AwaitExt 0, 0, Nothing, newMEnvs)
        `shouldBe` (AwaitExt 0, 0, Nothing, newMEnvs)

      it "AwaitInt -> AwaitInt#" $
        nst (AwaitInt 0, 0, Nothing, newMEnvs)
        `shouldBe` (AwaitInt 0, 0, Nothing, newMEnvs)

      it "Seq -> Seq#" $
        nst (Seq (AwaitInt 0) Nop, 0, Nothing, newMEnvs)
        `shouldBe` (Seq (AwaitInt 0) Nop, 0, Nothing, newMEnvs)

      it "Every -> Every#" $
        nst (Every 0 Nop, 0, Nothing, newMEnvs)
        `shouldBe` (Every 0 Nop, 0, Nothing, newMEnvs)

      it "Fin -> Fin#" $
        nst (Fin (Seq Nop Nop), 0, Nothing, newMEnvs)
        `shouldBe` (Fin (Seq Nop Nop), 0, Nothing, newMEnvs)

      it "And' -> And'#" $
        nst (And' (AwaitExt 0) (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` (And' (AwaitExt 0) (Fin Nop), 0, Nothing, newMEnvs)

      it "Or' -> Or'#" $
        nst (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, newMEnvs)
        `shouldBe` (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, newMEnvs)

      it "CanRun -> CanRun#" $
        nst (CanRun 5, 0, Nothing, newMEnvs)
        `shouldBe` (CanRun 5, 0, Nothing, newMEnvs)

    describe "Zero steps: No nst-rule applies" $ do
      it "Nop -> Nop#" $
        nst (Nop, 0, Nothing, newMEnvs)
        `shouldBe` (Nop, 0, Nothing, newMEnvs)

      it "Break -> Break#" $
        nst (Break, 0, Nothing, newMEnvs)
        `shouldBe` (Break, 0, Nothing, newMEnvs)

    describe "One+ steps" $ do
      it "EmitInt -> CanRun#" $
        let d = (EmitInt 8, 3, Nothing, newMEnvs)
            d' = (CanRun 3, 3, Just 8, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "CanRun -> Nop#" $
        let d = (CanRun 3, 3, Nothing, newMEnvs)
            d' = (Nop, 3, Nothing, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Nop; Nop; Nop; Break; Nop -> Break#" $
        let p = Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop
            d = (p, 0, Nothing, newMEnvs)
            d' = (Break, 0, Nothing, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Loop Break; Nop; Nop; EmitInt; Break -> CanRun#; Break" $
        let p = Loop Break `Seq` Nop `Seq` Nop `Seq` EmitInt 8 `Seq` Break
            d = (p, 3, Nothing, newMEnvs)
            d' = (Seq (CanRun 3) Break, 3, Just 8, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "(Loop Break; Nop) && (EmitInt; Nop) -> CanRun#; Nop" $
        let p = Seq (Loop Break) Nop `And` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, newMEnvs)
            d' = (Seq (CanRun 3) Nop, 3, Just 8, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "(Loop Break; Nop) || (EmitInt; Nop) -> Nop#" $
        let p = Seq (Loop Break) Nop `Or` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, newMEnvs)
            d' = (Nop, 3, Nothing, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "Loop ((Nop; AwaitInt) && (AwaitExt || Nop; Break)) -> Nop#" $
        let p = Loop ((Nop `Seq` AwaitInt 3)
                      `And` (AwaitExt 18 `Or` (Nop `Seq` Break)))
            d = (p, 0, Nothing, newMEnvs)
            d' = (Nop, 0, Nothing, newMEnvs) in
          (nst d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

  -- out1 ------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "transit: lvl == 0" $
        out1 (Nop, 0, Just 1, newMEnvs)
        `shouldBe` Just (Nop, 1, Nothing, newMEnvs)

      it "transit: lvl > 0" $
        out1 (Seq (AwaitInt 1) Break, 3, Just 1, newMEnvs)
        `shouldBe` Just (Seq Nop Break, 4, Nothing, newMEnvs)

      it "transit: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt 2) Break, 3, Just 1, newMEnvs)
        `shouldBe` Just (Seq (AwaitInt 2) Break, 4, Nothing, newMEnvs)

    -- pop --
    describe "pop" $ do
      it "nothing: lvl == 0" $
        out1 (Nop, 0, Nothing, newMEnvs)
        `shouldBe` Nothing

      it "transit: lvl > 0 && nst-irreducible" $
        out1 (Nop, 33, Nothing, newMEnvs)
        `shouldBe` Just (Nop, 32, Nothing, newMEnvs)

      it "nothing: lvl > 0 && not nst-irreducible" $
        out1 (Seq Nop Nop, 1, Nothing, newMEnvs)
        `shouldBe` Nothing

  -- out -------------------------------------------------------------------
  describe "out" $ do
    describe "Zero steps: No out-rule applies" $ do
      it "lvl == 0" $
        let d = (Nop, 0, Nothing, newMEnvs)
            d' = d in
          (out d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "not (isNstIrreducible p)" $
        let d = (Seq Nop Nop, 0, Nothing, newMEnvs)
            d' = d in
          (out d `shouldBe` d')
          >> (not (isNstIrreducible d') `shouldBe` True)

    describe "One+ steps: One+ pops" $ do
      it "lvl > 0" $
        let d = (Nop, 13, Nothing, newMEnvs)
            d' = (Nop, 0, Nothing, newMEnvs) in
          out d `shouldBe` d'

    describe "One+ steps: One push followed by one+ pops" $ do
      it "lvl == 0" $
        let d = (AwaitInt 3, 0, Just 3, newMEnvs)
            d' = (Nop, 0, Nothing, newMEnvs) in
          out d `shouldBe` d'

      it "lvl > 0" $
        let d = (AwaitInt 3, 88, Just 3, newMEnvs)
            d' = (Nop, 0, Nothing, newMEnvs) in
          out d `shouldBe` d'

  -- eval2 -----------------------------------------------------------------
  describe "eval2" $ do

    -- *** CHECK THESE *** --

    it "Nop; (AwaitInt 3) && Nop; Fin Nop -> Nop" $
      let p = (Nop `Seq` AwaitInt 3) `And` (Nop `Seq` Fin Nop) in
        eval2 (p, 0, Just 3, newMEnvs)
        `shouldBe` (AwaitInt 3 `And'` Fin Nop, 0, Nothing, newMEnvs)

    it "Nop; (AwaitInt 3) && Nop; (EmitInt 3) -> Nop" $
      let p = (Nop `Seq` AwaitInt 3) `And` (Nop `Seq` EmitInt 3) in
        eval2 (p, 0, Just 1, newMEnvs)
        `shouldBe` (Nop, 0, Nothing, newMEnvs)

  -- evalProg -----------------------------------------------------------------
  describe "evalProg" $ do

    it "var a; var ret; a=1; ret=a+10;" $
      let p = Seq (Var "a") (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10))))) in
        (evalProg p)
        `shouldBe` (Just 11)

    it "var a; {var ret; a=1; ret=a+10;}" $
      let p = Seq (Var "a") (Block (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p)
        `shouldBe` Nothing

    it "var ret; ret=1; {var ret; ret=99;}" $
      let p = Seq (Var "ret") (Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Seq (Var "ret") (Write "ret" (Const 99)))))) in
        (evalProg p)
        `shouldBe` (Just 1)

    it "var ret; var a; a=1; {var a; a=99;} ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Block (Seq (Var "a") (Write "a" (Const 99)))) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p)
        `shouldBe` (Just 11)

    it "var ret; ret=1; {ret=2;}" $
      let p = Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Write "ret" (Const 2)))) in
        (evalProg p)
        `shouldBe` (Just 2)

    it "var ret; var a; a=1; ({var a; a=99; awaitExt E} || nop); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Or (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Nop) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p)
        `shouldBe` (Just 11)

    it "var ret; ({ret=1; awaitExt E} || nop);" $
      let p = Seq (Var "ret") (Or (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Nop) in
        (evalProg p)
        `shouldBe` (Just 1)

    it "var ret; var a; a=1; loop ({var a; a=99; awaitExt E} && break); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Loop (And (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Break)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p)
        `shouldBe` (Just 11)

    it "var ret; loop ({ret=1; awaitExt E} && break);" $
      let p = Seq (Var "ret") (Loop (And (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Break))in
        (evalProg p)
        `shouldBe` (Just 1)
