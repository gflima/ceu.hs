module Ceu.Full.Clear where

import qualified Ceu.Grammar as G

import Ceu.Grammar.Check.Reachable (maybeTerminates)
import Ceu.Grammar.Check.Escape    (removeTrap)

clear :: String -> G.Stmt -> G.Stmt

clear "Or" (G.Trap (G.Par p1'@(G.Seq p1 (G.Escape 0)) p2'@(G.Seq p2 (G.Escape 0)))) =
  let t1 = maybeTerminates p1
      t2 = maybeTerminates p2
      p1'' = if t1 then p1' else p1
      p2'' = if t2 then p2' else p2
      ret  = (G.Trap (G.Par p1'' p2''))
  in
    if t1 || t2 then
      ret
    else
      removeTrap ret

clear id _ = error $ "unexpected clear case: " ++ id
