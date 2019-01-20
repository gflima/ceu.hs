module Ceu.Eval where

import Data.List  (find, intercalate)
import Data.Bool  (bool)
import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (type_, getAnn)
import Ceu.Grammar.Type as Type (Type(..), show')
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
    | Write  Loc Exp                    -- assignment statement
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
fromExp (B.Arg    _)      = Read "_arg"
fromExp (B.Unit   _)      = Unit
fromExp (B.Tuple  _ vs)   = Tuple (map fromExp vs)
fromExp (B.Call   _ f e)  = Call (fromExp f) (fromExp e)
fromExp (B.Func   _ z p)  = Func (fromStmt p)
fromExp (B.Read   z id)   = Read id' where
                              id' = case type_ z of
                                tp@(TypeF _ _) -> id ++ "__" ++ Type.show' tp
                                otherwise      -> id

fromStmt :: B.Stmt -> Stmt
fromStmt (B.Class  _ _ _ _ p)          = fromStmt p
fromStmt (B.Data   _ _ _ _ _ p)        = fromStmt p
fromStmt (B.Var _ id tp@(TypeF _ _) p) = Var (id++"__"++Type.show' tp, Nothing) (fromStmt p)
fromStmt (B.Var _ id _ p)              = Var (id,Nothing) (fromStmt p)
fromStmt (B.CallS  _ f e)              = CallS (fromExp f) (fromExp e)
fromStmt (B.Seq    _ p1 p2)            = Seq (fromStmt p1) (fromStmt p2)
fromStmt (B.If     _ e p1 p2)          = If (fromExp e) (fromStmt p1) (fromStmt p2)
fromStmt (B.Loop   _ p)                = Loop' (fromStmt p) (fromStmt p)
fromStmt (B.Ret    _ e)                = Ret (fromExp e)
fromStmt (B.Nop    _)                  = Nop

fromStmt (B.Write  _ loc e)            = Write (aux loc (type_ $ getAnn e)) (fromExp e)
  where
    aux LUnit          _          = LUnit
    aux LAny           _          = LAny
    aux (LTuple locs) (TypeN tps) = LTuple $ zipWith aux locs tps
    aux (LVar id)      tp         =
      case tp of
        tp@(TypeF _ _) -> LVar $ id ++ "__" ++ Type.show' tp
        otherwise      -> LVar $ id

fromStmt (B.Inst   _ _ _ imp p)        = aux (fromStmt imp) (fromStmt p)
  where
    aux Nop                p = p
    aux (Var vv (Seq x y)) p = Var vv (Seq x (aux y p))
    aux x p = error $ show (x,p)

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
        (Read "negate__(Int -> Int)",    Number x)                   -> Number (-x)
        (Read "+__((Int,Int) -> Int)",   Tuple [Number x, Number y]) -> Number (x+y)
        (Read "-__((Int,Int) -> Int)",   Tuple [Number x, Number y]) -> Number (x-y)
        (Read "*__((Int,Int) -> Int)",   Tuple [Number x, Number y]) -> Number (x*y)
        (Read "/__((Int,Int) -> Int)",   Tuple [Number x, Number y]) -> Number (x `div` y)
        (Read "==__((Int,Int) -> Bool)", Tuple [Number x, Number y]) -> Cons (bool "Bool.False" "Bool.True" (x == y))
        (Func p,        arg)                                        -> steps (p, ("_arg",Just arg):vars)
        otherwise -> error $ show (f,e')

    e         -> e

----------------------------------------------------------------------------

step :: Desc -> Desc

step (Var _  Nop,     vars)  = (Nop,        vars)
step (Var vv (Ret e), vars)  = (Ret e,      vv:vars)
step (Var vv p,       vars)  = (Var vv' p', vars') where (p',vv':vars') = step (p,vv:vars)

step (Write loc e,    vars)  = (Nop, aux vars loc e)
  where
    aux vars LUnit         _          = vars
    aux vars LAny          _          = vars
    aux vars (LVar var)    e          = envWrite vars var (envEval vars e)
    aux vars (LTuple locs) (Tuple es) = foldr (\(loc,e) vars' -> aux vars' loc e)
                                              vars
                                              (zip locs (map (envEval vars) es))

step (Seq Nop     q,  vars)  = (q,          vars)
step (Seq (Ret e) q,  vars)  = (Ret e,      vars)
step (Seq p       q,  vars)  = (Seq p' q,   vars') where (p',vars') = step (p,vars)

step (If exp p q,     vars)  =
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
