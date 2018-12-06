module Ceu.Grammar.Full.Clean where

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Stmt as G

import Ceu.Grammar.Check.Reachable (maybeTerminates)
import Ceu.Grammar.Check.Escape    (getEscapes, escapesAt1, removeTrap)

clean :: (Eq ann, Show ann) => String -> (G.Stmt ann) -> (Errors, G.Stmt ann)

clean "Or'" p = fin_or [] p
clean "Or"  p = fin_or [G.err_stmt_msg p "no trails terminate"] p

clean "Loop" s@(G.Trap _ p) = ([], if escapesAt1 p then s else removeTrap s)

clean "Spawn" p = (es1++es2,p') where
  (es1,p') =
    if maybeTerminates p then
      ([G.err_stmt_msg p "terminating `spawn`"], G.Seq (G.getAnn p) p (G.AwaitExt (G.getAnn p) "FOREVER"))
    else
      ([], p)
  es2 =
    let escs = (getEscapes p') in
      if escs == [] then
        []
      else
        [G.err_stmt_msg p "escaping `spawn`"] ++ (G.errs_stmts_msg_map (map fst escs) "escaping statement")

clean id p = error $ "unexpected clean case: " ++ id ++ "\n" ++ (show p)

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
