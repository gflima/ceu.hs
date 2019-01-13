module Ceu.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt    as G
import qualified Ceu.Grammar.TypeSys as T
import Debug.Trace

type Vars = [(ID_Var, Maybe Exp)]
type Desc = (Stmt, Vars)

data Stmt
    = Var   (ID_Var,Maybe Exp) Stmt    -- block with environment store
    | Write ID_Var Exp                 -- assignment statement
    | If    Exp Stmt Stmt              -- conditional
    | Seq   Stmt Stmt                  -- sequence
    | Nop                              -- dummy statement (internal)
    | Ret   Exp                        -- terminate program with exp
    | Loop' Stmt Stmt                  -- unrolled Loop (internal)
    deriving (Eq, Show)

infixr 1 `Seq`

fromGrammar :: G.Stmt -> Stmt
fromGrammar (G.Class _ _ _ _ p)     = fromGrammar p
fromGrammar (G.Inst _ _ _ _ p)      = fromGrammar p
fromGrammar (G.Data _ _ _ _ _ p)    = fromGrammar p
fromGrammar (G.Var _ id _ p)        = Var (id,Nothing) (fromGrammar p)
fromGrammar (G.Func _ _ _ p)        = (fromGrammar p)
fromGrammar (G.FuncI _ _ _ _ _)     = error "not implemented"
fromGrammar (G.Write _ (LVar id) e) = Write id e
fromGrammar (G.If _ e p1 p2)        = If e (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq _ p1 p2)         = Seq (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Loop _ p)            = Loop' (fromGrammar p) (fromGrammar p)
fromGrammar (G.Ret _ e)             = Ret e
fromGrammar (G.Nop _)               = Nop

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
    case vars of
        (var',val):vars'
            | var' == var -> case val of
                                Just v    -> v
                                otherwise -> error $ "envRead: uninitialized variable: " ++ var
            | otherwise   -> envRead vars' var
        []                -> error ("envRead: undeclared variable: " ++ var)

envEval :: Vars -> Exp -> Exp
envEval vars e = case e of
    Read  _ var     -> envRead vars var
{-
    Call  _ "negate" e -> negate $ envEval vars e
    Call  _ "+"  (Tuple _ [e1,e2]) -> (envEval vars e1) + (envEval vars e2)
    Call  _ "-"  (Tuple _ [e1,e2]) -> (envEval vars e1) - (envEval vars e2)
    Call  _ "*"  (Tuple _ [e1,e2]) -> (envEval vars e1) * (envEval vars e2)
    Call  _ "/"  (Tuple _ [e1,e2]) -> (envEval vars e1) `div` (envEval vars e2)
    Call  _ "==" (Tuple _ [e1,e2]) -> if (envEval vars e1) == (envEval vars e2) then 1 else 0
    Call  _ "<=" (Tuple _ [e1,e2]) -> if (envEval vars e1) <= (envEval vars e2) then 1 else 0
-}
    e               -> e

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
        (Cons _ "Bool.True") -> (p,         vars)
        otherwise            -> (q,         vars)

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
    ([], p) -> steps ((fromGrammar p), [])
    (es, _) -> error $ "compile error : " ++ show es
