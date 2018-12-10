module Ceu.Grammar.Full.Clean where

import Debug.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G

import Ceu.Grammar.Check (maybeTerminates, alwaysInstantaneous, getEscapes,
                          escapesAt0, removeTrap)

clean :: (Eq ann, Ann ann) => String -> (G.Stmt ann) -> (Errors, G.Stmt ann)

clean "And"
  s@(G.Trap z
    (G.Var _ "__and"
      (G.Seq _
        (G.Write _ "__and" (Const _ 0))
        (G.Par _
          (G.Seq _ p1 chk1)
          (G.Seq _ p2 chk2))
    )))
    | alwaysInstantaneous p1 = (es1++es2, removeTrap (G.Trap z (G.Seq z p1 p2)))
    -- | neverInstantaneous p1 && alwaysInstantaneous p2 = G.Par () p1 p2
    | otherwise              = (es1++es2, s)
  where
    es1 = if maybeTerminates p1 then [] else
            [toError p1 "trail must terminate"]
    es2 = if maybeTerminates p2 then [] else
            [toError p2 "trail must terminate"]

clean "Or'" p = fin_or [] p
clean "Or"  p = fin_or [toError p "no trails terminate"] p

clean "Loop" s@(G.Trap _ p) = ([], if escapesAt0 p then s else removeTrap s)

clean "Spawn" p = (es1++es2,p') where
  (es1,p') =
    if maybeTerminates p then
      ([toError p "terminating `spawn`"], G.Seq (G.getAnn p) p (G.AwaitExt (G.getAnn p) "FOREVER"))
    else
      ([], p)
  es2 =
    let escs = (getEscapes p') in
      if escs == [] then
        []
      else
        [toError p "escaping `spawn`"] ++ (errs_nodes_msg_map (map fst escs) "escaping statement")

clean id p = error $ "unexpected clean case: " ++ id ++ "\n" -- ++ (show p)

-------------------------------------------------------------------------------

fin_or err (G.Trap z1 (G.Par z2 p1'@(G.Seq _ p1 (G.Escape _ 0)) p2'@(G.Seq _ p2 (G.Escape _ 0)))) =
  let t1 = maybeTerminates p1
      t2 = maybeTerminates p2
      p1'' = if t1 then p1' else p1
      p2'' = if t2 then p2' else p2
      ret  = (G.Trap z1 (G.Par z2 p1'' p2''))
  in
    if t1 || t2 then
      ([], ret)
    else
      (err, removeTrap ret)
