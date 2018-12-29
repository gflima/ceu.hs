module Ceu.Grammar.Ann where

import Ceu.Grammar.Globals (Source, Trails, Errors)
import Ceu.Grammar.Type    (Type, checkTypes)

class (Show a, Eq a) => Ann a where
  getName   :: a -> String
  getType   :: a -> Type
  getSource :: a -> Source
  getN      :: a -> Int
  getTrails :: a -> Trails

  toError  :: a -> String -> String
  toError node msg = src ++ pre ++ msg where
    pre = let nm=getName node in if nm=="" then "" else ": "
    src = case getSource node of
      (_,0, 0)  -> ""
      (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

  toErrorTypes :: a -> Type -> Type -> Errors
  toErrorTypes s t1 t2 = if checkTypes t1 t2 then [] else
                            [toError s "types do not match"]

  toTrails0 :: a -> Int
  toTrails0 = fst . getTrails
  toTrailsN :: a -> Int
  toTrailsN = snd . getTrails

errs_anns_msg_map :: (Ann a) => [a] -> String -> Errors
errs_anns_msg_map anns msg = map (\ann -> (let nm=getName ann in if nm=="" then "" else nm++": ")
                                           ++ msg) anns
