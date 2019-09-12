module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

remSSetSIf :: Stmt -> Stmt

remSSetSIf (SSet z ini chk pat exp) = SMatch z ini chk exp [(SNop z,pat,SNop z)]
remSSetSIf (SIf  z exp p1 p2)       = SMatch z False False exp [
                                        (SNop z, EExp z (EVar z "_true"), p1),
                                        (SNop z, EAny z,                  p2)
                                      ]
remSSetSIf p = p

-------------------------------------------------------------------------------

remIni :: Stmt -> Stmt

remIni (SVarS z var tp ini p) = SVarS z var tp Nothing $
  case (ini,p) of
    (Nothing,_)      -> p
    (Just e, SNop _) -> SSet z True False (EVar z var) e
    (Just e, _)      -> SMatch z True False e [(SNop z,EVar z var,p)]
                        -- SSeq z (SSet z True False (EVar z var) e) p

remIni p = p
