module Ceu.Full.Trap where

import Ceu.Globals
import Ceu.Full.Grammar

compile :: Stmt -> (Errors, Stmt)
compile p = aux [] p where
  aux :: [Maybe ID_Var] -> Stmt -> (Errors,Stmt)
  aux vars (Var var fin p)   = (es, Var var fin p')
                               where
                                 (es,p') = aux vars p
  aux vars (Int id b p)      = (es, Int id b p')
                               where
                                 (es,p') = aux vars p
  aux vars (If exp p1 p2)    = (es1++es2, If exp p1' p2')
                               where
                                 (es1,p1') = (aux vars p1)
                                 (es2,p2') = (aux vars p2)
  aux vars (Seq p1 p2)       = (es1++es2, Seq p1' p2')
                               where
                                 (es1,p1') = aux vars p1
                                 (es2,p2') = aux vars p2
  aux vars (Loop p)          = (es, Loop p')
                               where
                                 (es,p') = aux vars p
  aux vars (Every evt exp p) = (es, Every evt exp p')
                               where
                                 (es,p') = aux vars p
  aux vars (And p1 p2)       = (es1++es2, And p1' p1')
                               where
                                 (es1,p1') = aux vars p1
                                 (es2,p2') = aux vars p2
  aux vars (Or p1 p2)        = (es1++es2, Or p1' p1')
                               where
                                 (es1,p1') = aux vars p1
                                 (es2,p2') = aux vars p2
  aux vars (Spawn p)         = (es, Spawn p')
                               where
                                 (es,p') = aux vars p
  aux vars (Pause evt p)     = (es, Pause evt p')
                               where
                                 (es,p') = aux vars p
  aux vars (Fin a b c)       = (es1++es2++es3, Fin p1' p2' p3')
                               where
                                 (es1,p1') = (aux vars a)
                                 (es2,p2') = (aux vars b)
                                 (es3,p3') = (aux vars c)
  aux vars (Async p)         = (es, Async p')
                               where
                                 (es,p') = aux vars p
  aux vars (Trap var p)      = (es, Trap' p')
                               where
                                 (es,p') = (aux (var:vars) p)
  aux vars s@(Escape (Just (var, Nothing)))
                             = (es, Escape' n)
                               where
                                 (es,n) = escape s (Just var) vars 0
  aux vars s@(Escape (Just (var, Just val)))
                             = (es, Seq (Write var val) (Escape' n))
                               where
                                 (es,n) = escape s (Just var) vars 0
  aux vars s@(Escape Nothing)  = (es, Escape' n)
                               where
                                 (es,n) = escape s Nothing vars 0
  aux vars p                 = ([], p)

escape :: Stmt -> (Maybe ID_Var) -> [Maybe ID_Var] -> Int -> (Errors, Int)
escape s var (var':lst) n
  | var == var' = ([], n)
  | otherwise   = escape s var lst (n+1)
escape s _ _ _  = ([err_stmt_msg s "no matching `trap`"], -1)   -- generate (Escape -1)
