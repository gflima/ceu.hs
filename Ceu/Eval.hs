module Ceu.Eval where

import Data.List  (find, intercalate)
import Data.Bool  (bool)
import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (type_, getAnn)
import Ceu.Grammar.Type as Type (Type(..), show', isRel, Relation(..))
import qualified Ceu.Grammar.Basic   as B
import qualified Ceu.Grammar.TypeSys as T

type Vars = [(ID_Var, Maybe Exp)]
type Desc = (Stmt, Vars)

error_terminate :: Int
error_match     :: Int
error_terminate = -1
error_match     = -2

data Exp
    = Error  Int
    | Number Int            -- 1
    | Cons   ID_Data_Hier Exp  -- True
    | Read   ID_Var         -- a ; xs
    | Unit                  -- ()
    | Tuple  [Exp]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Func   Stmt
    | Call   Exp Exp        -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

data Loc = LAny
         | LVar ID_Var
         | LUnit
         | LNumber Int
         | LCons ID_Data_Hier Loc
         | LTuple [Loc]
         | LExp Exp
  deriving (Eq, Show)

data Stmt
    = Var    (ID_Var,Maybe Exp) Stmt    -- block with environment store
    | Match  Loc Exp Stmt Stmt          -- match/assignment/if statement
    | CallS  Exp                        -- procedure call
    | Seq    Stmt Stmt                  -- sequence
    | Nop                               -- dummy statement (internal)
    | Ret    Exp                        -- terminate program with exp
    | Loop'  Stmt Stmt                  -- unrolled Loop (internal)
    deriving (Eq, Show)

infixr 1 `Seq`

fromExp :: B.Exp -> Exp
fromExp (B.Error  _ v)    = Error  v
fromExp (B.Number _ v)    = Number v
fromExp (B.Cons   _ id e) = Cons id (fromExp e)
fromExp (B.Arg    _)      = Read "_arg"
fromExp (B.Unit   _)      = Unit
fromExp (B.Tuple  _ vs)   = Tuple (map fromExp vs)
fromExp (B.Call   _ f e)  = Call (fromExp f) (fromExp e)
fromExp (B.Func   _ z p)  = Func (fromStmt p)
fromExp (B.Read   z id)   = Read id --' where
                              --id' = case type_ z of
                                --tp@(TypeF _ _) -> id ++ "__" ++ Type.show' tp
                                --otherwise      -> id

-------------------------------------------------------------------------------

fromLoc B.LAny             = LAny
fromLoc (B.LVar   id)      = LVar id
fromLoc B.LUnit            = LUnit
fromLoc (B.LNumber n)      = LNumber n
fromLoc (B.LCons  tps loc) = LCons tps (fromLoc loc)
fromLoc (B.LTuple locs)    = LTuple $ map fromLoc locs
fromLoc (B.LExp   exp)     = LExp (fromExp exp)

-------------------------------------------------------------------------------

fromStmt :: B.Stmt -> Stmt
fromStmt (B.Data   _ _ _ _ _ p)     = fromStmt p
fromStmt (B.Var _ id _ _ p)         = Var (id,Nothing) (fromStmt p)
fromStmt (B.CallS  _ e)             = CallS (fromExp e)
fromStmt (B.Seq    _ p1 p2)         = Seq (fromStmt p1) (fromStmt p2)
fromStmt (B.Loop   _ p)             = Loop' (fromStmt p) (fromStmt p)
fromStmt (B.Ret    _ e)             = Ret (fromExp e)
fromStmt (B.Nop    _)               = Nop
fromStmt (B.Match  _ _ loc e p1 p2) = Match (fromLoc loc) (fromExp e) (fromStmt p1) (fromStmt p2)

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
    Cons  id e' -> case envEval vars e' of
                    Error x -> Error x
                    e       -> Cons id e
    Read  var   -> envRead vars var
    Tuple es    -> let exps = map (envEval vars) es in
                    case find isError exps of
                      Nothing  -> Tuple exps
                      Just exp -> exp
                    where
                      isError (Error _) = True
                      isError _         = False

    Call  f e'  ->
      case (envEval vars f, envEval vars e') of
        (Error x, _)                                -> Error x
        (_, Error x)                                -> Error x
        (Read "print",  x)                          -> traceShowId x
        (Read "negate", Number x)                   -> Number (-x)
        (Read "+",      Tuple [Number x, Number y]) -> Number (x+y)
        (Read "-",      Tuple [Number x, Number y]) -> Number (x-y)
        (Read "*",      Tuple [Number x, Number y]) -> Number (x*y)
        (Read "/",      Tuple [Number x, Number y]) -> Number (x `div` y)
        (Read "==",     Tuple [Number x, Number y]) -> Cons (bool ["Bool","False"] ["Bool","True"] (x == y)) Unit
        (Read "<=",     Tuple [Number x, Number y]) -> Cons (bool ["Bool","False"] ["Bool","True"] (x <= y)) Unit
        (Read "<",      Tuple [Number x, Number y]) -> Cons (bool ["Bool","False"] ["Bool","True"] (x < y)) Unit
        (Func p,        arg)                        -> steps (p, ("_arg",Just arg):vars)
        otherwise                                   -> error $ show (f,e',vars)

    e         -> e

----------------------------------------------------------------------------

step :: Desc -> Desc

step (Var _  Nop,     vars)  = (Nop,        vars)
step (Var vv (Ret e), vars)  = (Ret e,      vv:vars)
step (Var vv p,       vars)  = (Var vv' p', vars') where (p',vv':vars') = step (p,vv:vars)

step (CallS e,        vars)  = (p,          vars) where
                                ret = envEval vars e
                                p   = case ret of
                                        Error v   -> Ret ret
                                        otherwise -> Nop

step (Match loc e p q,vars)  = case envEval vars e of
                                Error x -> (Ret (Error x), vars)
                                e'      -> f $ aux vars loc e'
  where
    aux vars LAny         _ = (Right True,            vars)
    aux vars (LVar id)    v = (Right True,            envWrite vars id v)
    aux vars LUnit        v = (Right True,            vars)
    aux vars (LNumber x)  v = (Right (Number x == v), vars)
    aux vars (LCons id l)
             (Cons id' e)   = if isRel SUP (TypeD id) (TypeD id') then
                                case envEval vars e of
                                  Error x -> (Left $ Error x, vars)
                                  e'      -> aux vars l e'
                              else
                                (Right False, vars)
    aux vars (LTuple ls)
             (Tuple es)     = foldr (\(loc,e) (b1,vars1) ->
                                      if b1/=(Right True) then (b1,vars1) else
                                        case envEval vars1 e of
                                          Error x -> (Left $ Error x, vars)
                                          e'      -> aux vars1 loc e')
                                    (Right True, vars)
                                    (zip ls es)
    aux vars (LExp x)     v = case envEval vars x of
                                Error x -> (Left  $ Error x, vars)
                                e'      -> (Right $ e' == v, vars)

    --aux x y z = error $ show (y,z)

    --err xp got = error $ "assignment does not match : expected '" ++ show xp ++
                                                 --"' : found '"    ++ show got ++ "'"

    f (Right True,  vars) = (p,       vars)
    f (Right False, vars) = (q,       vars)
    f (Left  err,   vars) = (Ret err, vars)

step (Seq Nop     q,  vars)  = (q,          vars)
step (Seq (Ret e) q,  vars)  = (Ret e,      vars)
step (Seq p       q,  vars)  = (Seq p' q,   vars') where (p',vars') = step (p,vars)

step (Loop' Nop     q, vars) = (Loop' q q,  vars)
step (Loop' (Ret e) q, vars) = (Ret e,      vars)
step (Loop' p q, vars)       = (Loop' p' q, vars') where (p',vars') = step (p,vars)

step p =  error $ "step: cannot advance : " ++ (show p)

----------------------------------------------------------------------------

steps :: Desc -> Exp
steps (Ret e, vars) = envEval vars e
steps d             = if (envRead vars "_steps") == (Number 1000) then
                        Error error_terminate
                      else
                        steps (step d') where (s,vars) = d
                                              d'       = (s,vars')
                                              vars'    = envWrite vars "_steps" (Number $ v+1)
                                              Number v = envRead vars "_steps"

go :: B.Stmt -> Exp
go p = case T.go p of
    ([], p) -> go' p
    (es, _) -> error $ "compile error : " ++ show es

go' :: B.Stmt -> Exp
go' p = steps (fromStmt p, [("_steps",Just $ Number 0)])
