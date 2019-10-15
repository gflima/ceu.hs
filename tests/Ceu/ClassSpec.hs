{-# LANGUAGE QuasiQuotes #-}

module Ceu.ClassSpec (main, spec) where

import Test.Hspec
import Text.RawString.QQ

import Ceu.Grammar.Ann (annz)

import Ceu.Grammar.Constraints
import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Full.Full
import Ceu.Grammar.Full.Compile.Class

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "G.combos:" $ do

    it "aaa" $
      (combos l0)
      `shouldBe` []

    it "bbb" $
      (combos [["Int"],["Obj"]])
      `shouldBe` [["Int","Obj"]]

    it "ccc" $
      (combos [["Int","Bool"]])
      `shouldBe` [["Int"],["Bool"]]

    it "ddd" $
      (combos [["Int","Bool"],["Obj"]])
      `shouldBe` [["Int","Obj"],["Bool","Obj"]]

    it "eee" $
      (combos [["Int"]])
      `shouldBe` [["Int"]]

    it "fff" $
      (combos [[],["Int"]])
      `shouldBe` []

  describe "combos':" $ do

    it "aaa" $
      (combos' 1 env [["IObj"]])
      `shouldBe` [[(TData False ["Obj"] [],[])]]

    it "bbb" $
      (combos' 1 env [["IEq"],["IObj"]])
      `shouldBe` [[(TData False ["Bool"] [],[]),(TData False ["Obj"] [],[])],[(TData False ["Int"] [],[]),(TData False ["Obj"] [],[])]]

    it "ccc" $
      (combos' 1 env [["IEq","IShow"]])
      `shouldBe` [[(TData False ["Bool"] [],[])],[(TData False ["Int"] [],[])]]

    it "ddd" $
      (combos' 1 env [["IEq","IShow"],["IObj"]])
      `shouldBe` [[(TData False ["Bool"] [],[]),(TData False ["Obj"] [],[])],[(TData False ["Int"] [],[]),(TData False ["Obj"] [],[])]]

  describe "test:" $ do

    it "unit" $
      (test env (TUnit,[]))
      `shouldBe` [[]]

    it "unit-1" $
      (test env (TUnit,[("a",["IEq"])]))
      `shouldBe`
        [[(TData False ["Bool"] [],[])],[(TData False ["Int"] [],[])]]

    it "unit" $
      (test env (TUnit,[("a",["IEq","IShow"]),("b",["IObj"])]))
      `shouldBe`
        [
          [(TData False ["Bool"] [],[]),(TData False ["Obj"] [],[])],
          [(TData False ["Int"]  [],[]),(TData False ["Obj"] [],[])]
        ]

    it "a" $
      (test env (TVar False "a",[("a",["IEq","IShow"]),("b",["IObj"])]))
      `shouldBe`
        [
          [(TData False ["Bool"] [],[]),(TData False ["Obj"] [],[])],
          [(TData False ["Int"] [],[]),(TData False ["Obj"] [],[])]
        ]

  where
    env = [
      (SInstS annz "IEq"   (TData False ["Bool"] [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IShow" (TData False ["Bool"] [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IEq"   (TData False ["Int"]  [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IShow" (TData False ["Int"]  [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IObj"  (TData False ["Obj"]  [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IShow" (TData False ["Obj"]  [],cz) (SNop annz) (SNop annz)),
      (SInstS annz "IEq"   (TTuple [TVar False "a",TVar False "a"], [("a",["IEq"])]) (SNop annz) (SNop annz))
     ]

    l0 :: [String]
    l0 = [[],[]]
