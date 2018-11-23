module Ceu.Full.Trap where

import Ceu.Globals
import Ceu.Full.Grammar

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux [] p) where
  aux :: [Maybe ID_Var] -> Stmt -> Stmt
  aux vars (Var var fin p)   = Var var fin (aux vars p)
  aux vars (Int id b p)      = Int id b (aux vars p)
  aux vars (If exp p1 p2)    = If exp (aux vars p1) (aux vars p2)
  aux vars (Seq p1 p2)       = Seq (aux vars p1) (aux vars p2)
  aux vars (Loop p)          = Loop (aux vars p)
  aux vars (Every evt exp p) = Every evt exp (aux vars p)
  aux vars (And p1 p2)       = And (aux vars p1) (aux vars p2)
  aux vars (Or p1 p2)        = Or (aux vars p1) (aux vars p2)
  aux vars (Spawn p)         = Spawn (aux vars p)
  aux vars (Pause evt p)     = Pause evt (aux vars p)
  aux vars (Fin a b c)       = Fin (aux vars a) (aux vars b) (aux vars c)
  aux vars (Async p)         = Async (aux vars p)
  aux vars (Trap var p)      = Trap' (aux (var:vars) p)
  aux vars s@(Escape _ _)    = escape vars s 0
  aux vars p                 = p

escape :: [Maybe ID_Var] -> Stmt -> Int -> Stmt
escape ((Just var):_) (Escape Nothing (Just val)) _ = Seq (Write var val) (Escape' 0)
escape (Nothing:_)    (Escape Nothing Nothing)    _ = Escape' 0
escape ((Just var'):l) s@(Escape (Just var) val) n
  | var == var' = case val of
                    (Just val') -> Seq (Write var val') (Escape' n)
                    Nothing     -> Escape' n
  | otherwise   = escape l s (n+1)
escape _ _ _ = Escape' (-1)

ins' :: Stmt -> Stmt
ins' p = (aux 0 p) where
  aux n (Var var Nothing p) = Var var Nothing (aux n p)
  aux n (Int int b p)       = Int int b (aux n p)
  aux n (If exp p1 p2)      = If exp (aux n p1) (aux n p2)
  aux n (Seq p1 p2)         = Seq (aux n p1) (aux n p2)
  aux n (Loop p)            = Loop (aux n p)
  aux n (Every evt var p)   = Every evt var (aux n p)
  aux n (Par' p1 p2)        = Par' (aux n p1) (aux n p2)
  aux n (Pause' var p)      = Pause' var (aux n p)
  aux n (Fin' p)            = Fin' (aux n p)
  aux n (Clean' id p)       = Clean' id (aux n p)
  aux n (Trap' p)           = Trap' (aux (n+1) p)
  aux n (Escape' k)
    | k >= n = (Escape' (k+1))
    | k <  n = (Escape' k)
  aux n p                   = p
