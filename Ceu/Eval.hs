module Ceu.Eval where

import Data.List  (find, intercalate)
import Data.Bool  (bool)

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann        (type_, getAnn)
import Ceu.Grammar.Type as T  (Type(..), isRel_, Relation(..))
import qualified Ceu.Grammar.Basic   as B
import qualified Ceu.Grammar.TypeSys as T

type Vars = [(ID_Var, Maybe Exp)]
type Desc = (Stmt, Vars)

error_terminate :: Int
error_match     :: Int
error_terminate = -1
error_match     = -2

data Exp
    = EError Int
    | EVar   ID_Var           -- a ; xs
    | EUnit                   -- ()
    | EData  ID_Data_Hier Exp -- True, X v (constants)
    | ECons  ID_Data_Hier     -- X         (functions)
    | ETuple [Exp]            -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc  Stmt
    | ECall  Exp Exp          -- f a ; f(a) ; f(1,2)
    | EAny
    | EExp   Exp
    | EMatch Exp Exp
    deriving (Eq, Show)

data Stmt
    = Var    (ID_Var,Maybe Exp) Stmt    -- block with environment store
    | Match  Exp [(Stmt,Exp,Stmt)]      -- match/assignment/if statement
    | CallS  Exp                        -- procedure call
    | Seq    Stmt Stmt                  -- sequence
    | Nop                               -- dummy statement (internal)
    | Ret    Exp                        -- terminate program with exp
    | Loop'  Stmt Stmt                  -- unrolled Loop (internal)
    deriving (Eq, Show)

infixr 1 `Seq`

fromExp :: B.Exp -> Exp
fromExp (B.EError _ v)   = EError  v
fromExp (B.EVar   _ id)  = EVar id
fromExp (B.EUnit  _)     = EUnit
fromExp (B.ECons  z id)  = case type_ z of
                            (TData _ _ TUnit, _) -> EData id EUnit
                            otherwise            -> ECons id
fromExp (B.ETuple _ vs)  = ETuple (map fromExp vs)
fromExp (B.EFunc  _ z p) = EFunc (fromStmt p)
fromExp (B.ECall  _ f e) = ECall (fromExp f) (fromExp e)
fromExp (B.EAny   _)     = EAny
fromExp (B.EArg   _)     = EVar "_arg"
fromExp (B.EExp   _ e)   = EExp (fromExp e)
fromExp (B.EMatch _ e p) = EMatch (fromExp e) (fromExp p)

-------------------------------------------------------------------------------

fromStmt :: B.Stmt -> Stmt
fromStmt (B.Data   _ _ _ p)         = fromStmt p
fromStmt (B.Var    _ id _ p)        = Var (id,Nothing) (fromStmt p)
fromStmt (B.CallS  _ e)             = CallS (fromExp e)
fromStmt (B.Seq    _ p1 p2)         = Seq (fromStmt p1) (fromStmt p2)
fromStmt (B.Loop   _ p)             = Loop' (fromStmt p) (fromStmt p)
fromStmt (B.Ret    _ e)             = Ret (fromExp e)
fromStmt (B.Nop    _)               = Nop
fromStmt (B.Match  _ _ exp cses)    = Match (fromExp exp) $
                                        map (\(ds,pt,st)->(fromStmt ds,fromExp pt,fromStmt st)) cses

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
      Nothing   -> EVar var   -- keep original (EVar "+")

read' :: String -> Int
read' x = read x

envEval :: Vars -> Exp -> Exp
envEval vars e = case e of
    EVar  var -> envRead vars var
    ETuple es -> let exps = map (envEval vars) es in
                  case find isError exps of
                    Nothing  -> ETuple exps
                    Just exp -> exp
                  where
                    isError (EError _) = True
                    isError _         = False

    EMatch exp pat -> case match vars pat (envEval vars exp) of
                        (Left  err,   _) -> err
                        (Right False, _) -> EData ["Bool","False"] EUnit
                        (Right True,  _) -> EData ["Bool","True"]  EUnit

    ECall  f e' ->
      case (envEval vars f, envEval vars e') of
        (EError x, _)                                   -> EError x
        (_, EError x)                                   -> EError x
        (EVar "print",  x)                              -> traceShowId x
        (EVar "negate", EData ["Int",x] EUnit)          -> EData ["Int",show (- (read x))] EUnit
        (EVar "+",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData ["Int",show (read x   +   read y)] EUnit
        (EVar "-",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData ["Int",show (read x   -   read y)] EUnit
        (EVar "*",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData ["Int",show (read x   *   read y)] EUnit
        (EVar "/",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData ["Int",show (read x `div` read y)] EUnit
        (EVar "rem",    ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData ["Int",show (read x `rem` read y)] EUnit
        (EVar "==",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData (bool ["Bool","False"] ["Bool","True"] (read' x == read' y)) EUnit
        (EVar "<=",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData (bool ["Bool","False"] ["Bool","True"] (read' x <= read' y)) EUnit
        (EVar "<",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> EData (bool ["Bool","False"] ["Bool","True"] (read' x < read' y))  EUnit
        (ECons id,       e)                             -> EData id (envEval vars e)
        (EFunc p,        arg)                           -> steps (p, ("_arg",Just arg):vars)
        --x                                               -> error $ show (x,f,e',vars)

    e         -> e

----------------------------------------------------------------------------

match :: Vars -> Exp -> Exp -> (Either Exp Bool, Vars)
match vars EAny        _ = (Right True, vars)
match vars (EVar id)   v = (Right True, envWrite vars id v)
match vars EUnit       v = (Right True, vars)
match vars (EData hrp _)
           (EData hre _) = (Right ret, vars) where
                            ret = T.isRel_ T.SUP (TData hrp [] TUnit) (TData hre [] TUnit)
match vars (ECall (ECons hrp) l)
           (EData hre e) = (ret', vars')  where
                            v1 = T.isRel_ T.SUP (TData hrp [] TUnit) (TData hre [] TUnit)
                            (ret2,vars') = match vars l e
                            ret' = case ret2 of
                              Left  x  -> Left  x
                              Right v2 -> Right (v1 && v2)
match vars (ETuple ps)
           (ETuple es)   = foldr
                            (\(loc,e) (b1,vars1) ->
                              if b1/=(Right True) then (b1,vars1) else
                                match vars1 loc e)
                            (Right True, vars)
                            (zip ps es)
match vars (EExp x)    v = case envEval vars x of
                            EError x -> (Left  $ EError x, vars)
                            e'       -> (Right $ e' == v, vars)

match x y z = error $ show (y,z)
--err xp got = error $ "assignment does not match : expected '" ++ show xp ++
                                             --"' : found '"    ++ show got ++ "'"

----------------------------------------------------------------------------

step :: Desc -> Desc

step (Var _  Nop,     vars)  = (Nop,        vars)
step (Var vv (Ret e), vars)  = (Ret e,      vv:vars)
step (Var vv p,       vars)  = (Var vv' p', vars') where (p',vv':vars') = step (p,vv:vars)

step (CallS e,        vars)  = (p,          vars) where
                                ret = envEval vars e
                                p   = case ret of
                                        EError v   -> Ret ret
                                        otherwise -> Nop

step (Match e cses,   vars)  = case envEval vars e of
                                EError x -> (Ret (EError x), vars)
                                e'       -> toDesc $ foldl (aux e') (Right False, vars, Nop) cses
  where
    toDesc :: (Either Exp Bool, Vars, Stmt) -> Desc
    toDesc (_, vars, stmt) = (stmt,vars)

    aux :: Exp -> (Either Exp Bool, Vars, Stmt) -> (Stmt,Exp,Stmt) -> (Either Exp Bool, Vars, Stmt)
    aux exp all@(ret,vars0,stmt) (ds,pat,stmt') =
      case (ret,ret') of
        (Left  err,  _)            -> all
        (Right True, _)            -> all
        (Right False, Left  err)   -> (ret', vars2, Ret err)
        (Right False, Right _)     -> (ret', vars2, stmt')
      where
        (ret', vars2) = match vars1 pat exp
        vars1 = f ds vars0 where
          f Nop        vars = vars
          f (Var id p) vars = id : (f p vars)

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
steps d             = if (envRead vars "_steps") == (EData ["Int",show 1000] EUnit) then
                        EError error_terminate
                      else
                        steps (step d') where
                          (s,vars)              = d
                          d'                    = (s,vars')
                          vars'                 = envWrite vars "_steps" (EData ["Int", show (read v+1)] EUnit)
                          EData ["Int",v] EUnit = envRead  vars "_steps"

go :: B.Stmt -> Exp
go p = case T.go p of
    ([], p) -> go' p
    (es, _) -> error $ "compile error : " ++ show es

go' :: B.Stmt -> Exp
go' p = steps (fromStmt p, [("_steps",Just $ EData ["Int","0"] EUnit)])
