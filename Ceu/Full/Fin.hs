module Ceu.Full.Fin where

import Ceu.Globals
import Ceu.Full.Grammar

-- compile:
-- (Fin x y z);A -> (or (Fin' p) A)
-- (Fin id p);A -> A ||| (Var (Or [(Fin p)] X)

compile :: Stmt -> (Errors, Stmt)
compile p = aux Nothing p where
  aux :: (Maybe ID_Evt) -> Stmt -> (Errors,Stmt)
  aux pse (Var var (Just (x,y,z)) p) = aux pse (Var var Nothing (Seq (Fin x y z) p))
  aux pse (Var var Nothing p)        = (es, Var var Nothing p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Int id b p)               = (es, Int id b p')
                                        where
                                          (es,p') = aux pse p
  aux pse (If exp p1 p2)             = (es1++es2, If exp p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2

  aux pse (Seq (Fin x y z) p)        = (es'++esX++esY++esZ++esP, Or' p' (Par yz (Fin' x')))
    where
      (esX,x') = aux pse x
      (esY,y') = aux pse y
      (esZ,z') = aux pse z
      (esP,p') = aux pse p

      (es',yz) = case (pse,y,z) of
        (Nothing,  Nop, Nop) -> ([], Nop)
        (Nothing,  _,   _)   -> (["unexpected `pause`/`resume` statement"], Nop)
        (Just evt, _,   _)   -> ([], Par
                                      (Every evt Nothing y')
                                      (Every ("__pause_int_"++evt) Nothing z'))

  aux pse (Seq p1 p2)                = (es1++es2, Seq p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Loop p)                   = (es, Loop p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Every evt exp p)          = (es, Every evt exp p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Par p1 p2)                = (es1++es2, Par p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (And p1 p2)                = (es1++es2, And p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Or p1 p2)                 = (es1++es2, Or p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Spawn p)                  = (es, Spawn p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Pause evt p)              = (es, Pause evt p')
                                        where
                                          (es,p') = (aux (Just evt) p)
  aux pse s@(Fin _ _ _)              = ([err_stmt_msg s "unexpected `finalize`"]++es, p')
                                        where
                                          (es,p') = aux pse (Seq s Nop)
  aux pse (Async p)                  = (es, Async p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Trap' p)                  = (es, Trap' p')
                                        where
                                          (es,p') = aux pse p
  aux pse p                          = ([], p)

