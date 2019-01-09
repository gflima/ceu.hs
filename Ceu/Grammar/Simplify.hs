module Ceu.Grammar.Simplify where

import Debug.Trace
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt (Stmt(..))

simplify :: Stmt -> Stmt

simplify (Var z id tp p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    (Seq z2 (AwaitInp z3 inp) (Seq z4 (Write z5 wrt (Read z6 "_INPUT")) p'')) ->
        (Seq z2 (AwaitInp z3 inp) (Var z id tp (Seq z4 (Write z5 wrt (Read z6 "_INPUT")) p'')))
    otherwise   -> Var z id tp p'
  where p' = simplify p

simplify (Inp z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Inp z id p'
  where p' = simplify p

simplify (Out z id tp p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Out z id tp p'
  where p' = simplify p

simplify (Evt z id p) =
  case p' of
    Nop z'      -> Nop z'
    Escape z' n -> Escape z' n
    otherwise   -> Evt z id p'
  where p' = simplify p

simplify (Func  z id tp     p) = Func  z id tp (simplify p)
simplify (FuncI z id tp imp p) = FuncI z id tp (simplify imp) (simplify p)

simplify (Write z _ (Unit _)) = Nop z

simplify (If z exp p q) =
  if p' == q' then p' else (If z exp p' q')
  where p' = simplify p
        q' = simplify q

-- normal form: (Seq x (Seq y (Seq z ...)))
simplify (Seq z1 (Seq z2 p1 p2) p3) = simplify $ Seq z1 p1 (Seq z2 p2 p3)
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
