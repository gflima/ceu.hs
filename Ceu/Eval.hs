module Ceu.Eval where

import Data.List  (find)
import Debug.Trace

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Basic   as B
import qualified Ceu.Grammar.TypeSys as T

type Vars = [(ID_Var, Maybe Exp)]
type Desc = (Stmt, Vars)

data Exp
    = Number Int            -- 1
    | Cons   ID_Type        -- True
    | Read   ID_Var         -- a ; xs
    | Unit                  -- ()
    | Tuple  [Exp]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Func   Stmt
    | Call   Exp Exp        -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

data Stmt
    = Var    (ID_Var,Maybe Exp) Stmt    -- block with environment store
    | Write  ID_Var Exp                 -- assignment statement
    | CallS  Exp Exp                    -- procedure call
    | If     Exp Stmt Stmt              -- conditional
    | Seq    Stmt Stmt                  -- sequence
    | Nop                               -- dummy statement (internal)
    | Ret    Exp                        -- terminate program with exp
    | Loop'  Stmt Stmt                  -- unrolled Loop (internal)
    deriving (Eq, Show)

infixr 1 `Seq`

fromExp :: B.Exp -> Exp
fromExp (B.Number _ v)    = Number v
fromExp (B.Cons   _ id)   = Cons id
fromExp (B.Read   _ id)   = Read id
fromExp (B.Unit   _)      = Unit
fromExp (B.Tuple  _ vs)   = Tuple (map fromExp vs)
fromExp (B.Func   _ _ p)  = Func (fromStmt p)
fromExp (B.Call   _ f e)  = Call (fromExp f) (fromExp e)

fromStmt :: B.Stmt -> Stmt
fromStmt (B.Class  _ _ _ _ p)     = fromStmt p
fromStmt (B.Inst   _ _ _ _ p)     = fromStmt p
fromStmt (B.Data   _ _ _ _ _ p)   = fromStmt p
fromStmt (B.Var    _ id _ p)      = Var (id,Nothing) (fromStmt p)
fromStmt (B.Write  _ (LVar id) e) = Write id (fromExp e)
fromStmt (B.CallS  _ f e)         = CallS (fromExp f) (fromExp e)
fromStmt (B.If     _ e p1 p2)     = If (fromExp e) (fromStmt p1) (fromStmt p2)
fromStmt (B.Seq    _ p1 p2)       = Seq (fromStmt p1) (fromStmt p2)
fromStmt (B.Loop   _ p)           = Loop' (fromStmt p) (fromStmt p)
fromStmt (B.Ret    _ e)           = Ret (fromExp e)
fromStmt (B.Nop    _)             = Nop

----------------------------------------------------------------------------

envWrite :: Vars -> ID_Var -> Exp -> Vars
envWrite vars var val =
    case vars of
        (var',val'):vars'
            | var == var' -> (var,Just val):vars'
            | otherwise   -> (var',val'):(envWrite vars' var val)
        []                -> error ("envWrite: undeclared variable: " ++ var)

envRead :: Vars -> ID_Var -> Exp
envRead vars var =
  case find (\(var',_)->var'==var) vars of
    Nothing      -> error ("envRead: undeclared variable: " ++ var)
    Just (_,val) -> case val of
      Just val' -> val'
      Nothing   -> Read var   -- keep original (Read "+")

envEval :: Vars -> Exp -> Exp
envEval vars e = case e of
    Read var  -> envRead vars var
    Tuple es' -> Tuple $ map (envEval vars) es'
    Call f e' ->
      case (envEval vars f, envEval vars e') of
        (Read "negate", Number x)                   -> Number (-x)
        (Read "+",      Tuple [Number x, Number y]) -> Number (x+y)
        (Read "-",      Tuple [Number x, Number y]) -> Number (x-y)
        (Func p,        arg)                        -> steps (p, ("_arg",Just arg):vars)
        otherwise -> error $ show (f,e')

    e         -> e

{-
    Call  _ "negate" e -> negate $ envEval vars e
    Call  _ "+"  (Tuple _ [e1,e2]) -> (envEval vars e1) + (envEval vars e2)
    Call  _ "-"  (Tuple _ [e1,e2]) -> (envEval vars e1) - (envEval vars e2)
    Call  _ "*"  (Tuple _ [e1,e2]) -> (envEval vars e1) * (envEval vars e2)
    Call  _ "/"  (Tuple _ [e1,e2]) -> (envEval vars e1) `div` (envEval vars e2)
    Call  _ "==" (Tuple _ [e1,e2]) -> if (envEval vars e1) == (envEval vars e2) then 1 else 0
    Call  _ "<=" (Tuple _ [e1,e2]) -> if (envEval vars e1) <= (envEval vars e2) then 1 else 0
-}

----------------------------------------------------------------------------

step :: Desc -> Desc

step (Var _  Nop,     vars)  = (Nop,        vars)
step (Var vv (Ret e), vars)  = (Ret e,      vv:vars)
step (Var vv p,       vars)  = (Var vv' p', vars') where (p',vv':vars') = step (p,vv:vars)

step (Write var e, vars)     = (Nop,        envWrite vars var (envEval vars e))

step (Seq Nop     q, vars)   = (q,          vars)
step (Seq (Ret e) q, vars)   = (Ret e,      vars)
step (Seq p       q, vars)   = (Seq p' q,   vars') where (p',vars') = step (p,vars)

step (If exp p q,    vars)   =
    case envEval vars exp of
        (Cons "Bool.True")  -> (p,          vars)
        otherwise           -> (q,          vars)

step (Loop' Nop     q, vars) = (Loop' q q,  vars)
step (Loop' (Ret e) q, vars) = (Ret e,      vars)
step (Loop' p q, vars)       = (Loop' p' q, vars') where (p',vars') = step (p,vars)

step p =  error $ "step: cannot advance : " ++ (show p)

----------------------------------------------------------------------------

steps :: Desc -> Exp
steps (Ret e, vars) = envEval vars e
steps d             = steps (step d)

go :: B.Stmt -> Exp
go p = case T.go p of
    ([], p) -> steps (fromStmt p, [])
    (es, _) -> error $ "compile error : " ++ show es
