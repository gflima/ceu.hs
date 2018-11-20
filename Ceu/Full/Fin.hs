module Ceu.Full.Fin where

import Ceu.Globals
import Ceu.Full.Grammar

-- remove:
-- (Fin x y z);A -> (or (Fin' p) A)
-- (Fin id p);A -> A ||| (Var (Or [(Fin p)] X)

remove :: Stmt -> Stmt
remove p = rF Nothing p where
  rF :: (Maybe ID_Evt) -> Stmt -> Stmt
  rF pse (Var var (Just (x,y,z)) p) = rF pse (Var var Nothing (Seq (Fin x y z) p))
  rF pse (Var var Nothing p)       = Var var Nothing (rF pse p)
  rF pse (Int id b p)              = Int id b (rF pse p)
  rF pse (If exp p1 p2)            = If exp (rF pse p1) (rF pse p2)

  rF pse (Seq (Fin x y z) p)       = Or (rF pse p) (And (rF pse yz) (Fin' (rF pse x)))
    where
      yz = case (pse,y,z) of
        (Nothing,  Nop, Nop) -> Nop
        (Nothing,  _,   _)   -> error "remFin: unexpected pause/resume statement"
        (Just evt, y,   z)   -> And
                                  (Every evt Nothing y)
                                  (Every ("__pause_int_"++evt) Nothing z)

  rF pse (Seq p1 p2)               = Seq (rF pse p1) (rF pse p2)
  rF pse (Loop p)                  = Loop (rF pse p)
  rF pse (Every evt exp p)         = Every evt exp (rF pse p)
  rF pse (And p1 p2)               = And (rF pse p1) (rF pse p2)
  rF pse (Or p1 p2)                = Or (rF pse p1) (rF pse p2)
  rF pse (Spawn p)                 = Spawn (rF pse p)
  rF pse (Pause evt p)             = Pause evt (rF (Just evt) p)
  rF pse (Fin _ _ _)               = error "remove: unexpected statement (Fin)"
  rF pse (Async p)                 = Async (rF pse p)
  rF pse p                         = p

