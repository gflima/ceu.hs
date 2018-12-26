module Ceu.Grammar.Simplify where

import Ceu.Grammar.Stmt

simplify :: (Eq ann) => (Stmt ann) -> (Stmt ann)

simplify (Var z id tp p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Var z id tp p'
  where p' = simplify p

simplify (Inp z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Inp z id p'
  where p' = simplify p

simplify (Out z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Out z id p'
  where p' = simplify p

simplify (Evt z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Evt z id p'
  where p' = simplify p

simplify (If z exp p q) =
  if p' == q' then p' else (If z exp p' q')
  where p' = simplify p
        q' = simplify q

simplify (Seq z p q) =
  case (p',q') of
    (Nop _,      q')  -> q'
    (p',       Nop _) -> p'
    (Escape z' n, q') -> Escape z' n
    otherwise         -> Seq z p' q'
  where p' = simplify p
        q' = simplify q

simplify (Loop z p) =
  case p' of
    Escape z' n -> Escape z' n
    otherwise   -> Loop z p'
  where p' = simplify p

simplify (Every z evt p) = (Every z evt (simplify p))   -- cannot contain `Escape`

simplify (Par z p q) =
  case (p',q') of
    (Halt _, q') -> q'
    (p', Halt _) -> p'
    (Escape z' n, q')          -> Escape z' n
    otherwise                  -> Par z p' q'
  where p' = simplify p
        q' = simplify q

simplify (Pause z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Pause z id p'
  where p' = simplify p

simplify (Fin z p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Fin z p'
  where p' = simplify p

simplify (Trap z p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' 0 -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Trap z p'
  where
    p' = simplify p

simplify p = p
