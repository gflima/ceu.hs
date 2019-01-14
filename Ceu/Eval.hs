module Ceu.Eval where

import Data.List (find)
import Debug.Trace

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Exp     as E
import qualified Ceu.Grammar.Stmt    as G
import qualified Ceu.Grammar.TypeSys as T

type Vars = [(ID_Var, Maybe Exp)]
type Desc = (Stmt, Vars)

data Exp
    = Number Int            -- 1
    | Cons   ID_Type        -- True
    | Read   ID_Var         -- a ; xs
    | Unit                  -- ()
    | Tuple  [Exp]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | SCall  ID_Func Exp    -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

data Stmt
    = Var    (ID_Var,Maybe Exp) Stmt    -- block with environment store
    | Write  ID_Var Exp                 -- assignment statement
    | SCallS ID_Func Exp                -- procedure call
    | If     Exp Stmt Stmt              -- conditional
    | Seq    Stmt Stmt                  -- sequence
    | Nop                               -- dummy statement (internal)
    | Ret    Exp                        -- terminate program with exp
    | Loop'  Stmt Stmt                  -- unrolled Loop (internal)
    deriving (Eq, Show)

infixr 1 `Seq`

fromExp :: E.Exp -> Exp
fromExp (E.Number _ v)    = Number v
fromExp (E.Cons   _ id)   = Cons id
fromExp (E.Read   _ id)   = Read id
fromExp (E.Unit   _)      = Unit
fromExp (E.Tuple  _ vs)   = Tuple (map fromExp vs)
fromExp (E.SCall  _ id e) = SCall id (fromExp e)

fromStmt :: G.Stmt -> Stmt
fromStmt (G.Class  _ _ _ _ p)     = fromStmt p
fromStmt (G.Inst   _ _ _ _ p)     = fromStmt p
fromStmt (G.Data   _ _ _ _ _ p)   = fromStmt p
fromStmt (G.Var    _ id _ p)      = Var (id,Nothing) (fromStmt p)
fromStmt (G.Func   _ _ _ p)       = (fromStmt p)
fromStmt (G.FuncI  _ _ _ _ _)     = error "not implemented"
fromStmt (G.Write  _ (LVar id) e) = Write id (fromExp e)
fromStmt (G.SCallS _ id e)        = SCallS id (fromExp e)
fromStmt (G.If     _ e p1 p2)     = If (fromExp e) (fromStmt p1) (fromStmt p2)
fromStmt (G.Seq    _ p1 p2)       = Seq (fromStmt p1) (fromStmt p2)
fromStmt (G.Loop   _ p)           = Loop' (fromStmt p) (fromStmt p)
fromStmt (G.Ret    _ e)           = Ret (fromExp e)
fromStmt (G.Nop    _)             = Nop

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
    Nothing         -> error ("envRead: undeclared variable: " ++ var)
    Just (var',val) -> case val of
                        Just v    -> v
                        otherwise -> error $ "envRead: uninitialized variable: " ++ var

envEval :: Vars -> Exp -> Exp
envEval vars e = case e of
    Read  var    -> envRead vars var
    SCall func e -> envRead vars func
{-
    Call  _ "negate" e -> negate $ envEval vars e
    Call  _ "+"  (Tuple _ [e1,e2]) -> (envEval vars e1) + (envEval vars e2)
    Call  _ "-"  (Tuple _ [e1,e2]) -> (envEval vars e1) - (envEval vars e2)
    Call  _ "*"  (Tuple _ [e1,e2]) -> (envEval vars e1) * (envEval vars e2)
    Call  _ "/"  (Tuple _ [e1,e2]) -> (envEval vars e1) `div` (envEval vars e2)
    Call  _ "==" (Tuple _ [e1,e2]) -> if (envEval vars e1) == (envEval vars e2) then 1 else 0
    Call  _ "<=" (Tuple _ [e1,e2]) -> if (envEval vars e1) <= (envEval vars e2) then 1 else 0
-}
    e         -> e

----------------------------------------------------------------------------

step :: Desc -> Desc

step (Var _  Nop,     vars)  = (Nop,        vars)
step (Var _  (Ret e), vars)  = (Ret e,      vars)
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

go :: G.Stmt -> Exp
go p = case T.go p of
    ([], p) -> steps ((fromStmt p), [])
    (es, _) -> error $ "compile error : " ++ show es
