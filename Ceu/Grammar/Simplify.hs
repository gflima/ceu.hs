module Ceu.Grammar.Simplify where

import Ceu.Grammar.Grammar

simplify :: Stmt -> Stmt

simplify (Var id p) =
  case p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Var id p'
  where p' = simplify p

simplify (Int id p) =
  case p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Int id p'
  where p' = simplify p

simplify (If exp p q) =
  if p' == q' then p' else (If exp p' q')
  where p' = simplify p
        q' = simplify q

simplify (Seq p q) =
  case (p',q') of
    (Nop,      q')  -> q'
    (p',       Nop) -> p'
    (Escape n, q')  -> Escape n
    otherwise       -> Seq p' q'
  where p' = simplify p
        q' = simplify q

simplify (Loop p) =
  case p' of
    Escape n  -> Escape n
    otherwise -> Loop p'
  where p' = simplify p

simplify (Every evt p) = (Every evt (simplify p))   -- cannot contain `Escape`

simplify (Par p q) =
  case (p',q') of
    (Nop,   q')    -> q'
    (p',    Nop)   -> p'
    (Escape n, q') -> Escape n
    otherwise      -> Par p' q'
  where p' = simplify p
        q' = simplify q

simplify (Pause id p) =
  case p' of
    Nop       -> Nop
    Escape n  -> Escape n
    otherwise -> Pause id p'
  where p' = simplify p

simplify (Fin p) =
  case p' of
    Nop       -> Nop
    otherwise -> Fin p'
  where p' = simplify p

simplify (Trap p) =
  case p' of
    Nop       -> Nop
    Escape 0  -> Nop
    Escape n  -> Escape n
    otherwise -> Trap p'
  where p' = simplify p

simplify p = p

