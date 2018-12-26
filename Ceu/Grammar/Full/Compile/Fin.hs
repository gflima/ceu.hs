module Ceu.Grammar.Full.Compile.Fin where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

-- compile:
-- (Fin f1 f2 f3);A -> (or (Fin' p) A)
-- (Fin id p);A -> A ||| (Var' (Or [(Fin p)] X)

compile :: (Ann ann) => (Stmt ann) -> (Errors, Stmt ann)
compile p = aux Nothing p where
  aux :: (Ann ann) => (Maybe ID_Evt) -> (Stmt ann) -> (Errors, Stmt ann)
  aux pse (Var' z var tp (Just (f1,f2,f3)) p) = aux pse (Var' z var tp Nothing (Seq z (Fin z f1 f2 f3) p))
  aux pse (Var' z var tp Nothing p)   = (es, Var' z var tp Nothing p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Inp' z id b p)             = (es, Inp' z id b p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Out' z id b p)             = (es, Out' z id b p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Evt' z id b p)             = (es, Evt' z id b p')
                                        where
                                          (es,p') = aux pse p
  aux pse (If z exp p1 p2)            = (es1++es2, If z exp p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2

  aux pse (Seq z1 (Fin z2 f1 f2 f3) p)  = (es'++esF1++esF2++esF3++esP, Or' z1 p' (Par z1 f23 (Fin' z2 f1')))
    where
      (esF1,f1') = aux pse f1
      (esF2,f2') = aux pse f2
      (esF3,f3') = aux pse f3
      (esP, p')  = aux pse p

      (es',f23) = case (pse,f2,f3) of
        (Nothing,  Nop _, Nop _) -> ([], Halt z2)
        (Nothing,  _,   _)   -> (["unexpected `pause`/`resume` statement"], Nop z2)
        (Just evt, _,   _)   -> ([], Par z2
                                      (Every z2 evt Nothing f2')
                                      (Every z2 ("__pause_int_"++evt) Nothing f3'))

  aux pse (Seq z p1 p2)               = (es1++es2, Seq z p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Loop z p)                  = (es, Loop z p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Every z evt exp p)         = (es, Every z evt exp p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Par z p1 p2)               = (es1++es2, Par z p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (And z p1 p2)               = (es1++es2, And z p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Or z p1 p2)                = (es1++es2, Or z p1' p2')
                                        where
                                          (es1,p1') = aux pse p1
                                          (es2,p2') = aux pse p2
  aux pse (Spawn z p)                 = (es, Spawn z p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Pause z evt p)             = (es, Pause z evt p')
                                        where
                                          (es,p') = (aux (Just evt) p)
  aux pse s@(Fin z _ _ _)             = ([toError s "unexpected `finalize`"]++es, p')
                                        where
                                          (es,p') = aux pse (Seq z s (Nop z))
  aux pse (Async z p)                 = (es, Async z p')
                                        where
                                          (es,p') = aux pse p
  aux pse (Trap' z p)                 = (es, Trap' z p')
                                        where
                                          (es,p') = aux pse p
  aux pse p                           = ([], p)

