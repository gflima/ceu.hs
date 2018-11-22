module Ceu.Full.Clean where

import Ceu.Globals
import qualified Ceu.Grammar as G

import Ceu.Grammar.Check.Reachable (maybeTerminates)
import Ceu.Grammar.Check.Escape    (escapesAt1, removeTrap)

clean :: String -> G.Stmt -> (Errors, G.Stmt)

clean "Or" (G.Trap (G.Par p1'@(G.Seq p1 (G.Escape 0)) p2'@(G.Seq p2 (G.Escape 0)))) =
  let t1 = maybeTerminates p1
      t2 = maybeTerminates p2
      p1'' = if t1 then p1' else p1
      p2'' = if t2 then p2' else p2
      ret  = (G.Trap (G.Par p1'' p2''))
  in
    if t1 || t2 then
      ([], ret)
    else
      ([], removeTrap ret)

clean "Loop" s@(G.Trap p) = ([], if escapesAt1 p then s else p)

clean "Spawn" p =
  if maybeTerminates p then
    (["terminating `spawn`"], G.Seq p (G.AwaitExt "FOREVER"))
  else
    ([], p)

clean id _ = error $ "unexpected clean case: " ++ id
