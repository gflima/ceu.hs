module Ceu.Grammar.Simplify where

import Ceu.Grammar.Stmt

simplify :: Stmt -> Stmt
simplify p = newStmt $ aux $ getStmt' p

aux (Var id p) =
  case getStmt' p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Var id p'
  where p' = simplify p

aux (Int id p) =
  case getStmt' p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Int id p'
  where p' = simplify p

aux (If exp p q) =
  if p' == q' then getStmt' p' else (If exp p' q')
  where p' = simplify p
        q' = simplify q

aux (Seq p q) =
  case (getStmt' p', getStmt' q') of
    (Nop,      q')  -> q'
    (p',       Nop) -> p'
    (Escape n, q')  -> Escape n
    otherwise       -> Seq p' q'
  where p' = simplify p
        q' = simplify q

aux (Loop p) =
  case getStmt' p' of
    Escape n  -> Escape n
    otherwise -> Loop p'
  where p' = simplify p

aux (Every evt p) = (Every evt (simplify p))   -- cannot contain `Escape`

aux (Par p q) =
  case (getStmt' p', getStmt' q') of
    (Nop,   q')    -> q'
    (p',    Nop)   -> p'
    (Escape n, q') -> Escape n
    otherwise      -> Par p' q'
  where p' = simplify p
        q' = simplify q

aux (Pause id p) =
  case getStmt' p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Pause id p'
  where p' = simplify p

aux (Fin p) =
  case getStmt' p' of
    Nop       -> Nop
    otherwise -> Fin p'
  where p' = simplify p

aux (Trap p) =
  case getStmt' p' of
    Nop       -> Nop
    Escape 0  -> Nop
    Escape n  -> Escape n
    otherwise -> Trap p'
  where p' = simplify p

aux p = p

