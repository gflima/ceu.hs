module Ceu.Full.Trap where

import Ceu.Globals
import Ceu.Full.Grammar

remove :: Stmt -> Stmt
remove p = aux [] p where
  aux :: [Maybe ID_Var] -> Stmt -> Stmt
  aux vars (Var var fin p)                  = Var var fin (aux vars p)
  aux vars (Int id b p)                     = Int id b (aux vars p)
  aux vars (If exp p1 p2)                   = If exp (aux vars p1) (aux vars p2)
  aux vars (Seq p1 p2)                      = Seq (aux vars p1) (aux vars p2)
  aux vars (Loop p)                         = Loop (aux vars p)
  aux vars (Every evt exp p)                = Every evt exp (aux vars p)
  aux vars (And p1 p2)                      = And (aux vars p1) (aux vars p2)
  aux vars (Or p1 p2)                       = Or (aux vars p1) (aux vars p2)
  aux vars (Spawn p)                        = Spawn (aux vars p)
  aux vars (Pause evt p)                    = Pause evt (aux vars p)
  aux vars (Fin a b c)                      = Fin (aux vars a) (aux vars b) (aux vars c)
  aux vars (Async p)                        = Async (aux vars p)
  aux vars (Trap var p)                     = Trap' (aux (var:vars) p)
  aux vars (Escape (Just (var, Nothing)))   = Escape' (escape (Just var) vars 0)
  aux vars (Escape (Just (var, Just val)))  = Seq (Write var val) (Escape' (escape (Just var) vars 0))
  aux vars (Escape Nothing)                 = Escape' (escape Nothing vars 0)
  aux vars p                                = p

escape :: (Maybe ID_Var) -> [Maybe ID_Var] -> Int -> Int
escape var (var':lst) n
  | var == var' = n
  | otherwise   = escape var lst (n+1)
escape _ _ _    = error "no matching `trap`"
