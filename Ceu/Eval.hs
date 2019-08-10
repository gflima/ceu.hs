module Ceu.Eval where

import Data.List  (find, intercalate)
import Data.Bool  (bool)

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann        (typec, getAnn)
import Ceu.Grammar.Type as T  (Type(..), isRel, Relation(..))
import qualified Ceu.Grammar.Basic   as B
import qualified Ceu.Grammar.TypeSys as T

type Vars = [(ID_Var, Maybe Exp)]

type DescS = (Stmt, Vars)
type DescE = (Exp,  Vars)

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
    | EFunc  Exp Stmt
    | EFNew  Exp Exp
    | ECall  Exp Exp          -- f a ; f(a) ; f(1,2)
    | EAny
    | EExp   Exp
    | EMatch Exp Exp
    | ERefRef Exp            -- &a
    | ERefDer Exp            -- *&a
    | ERefIni Exp            -- a =
    deriving (Eq, Show)

data Stmt
    = SVar    ID_Var Stmt                -- var declaration with its scope
    | SMatch  Exp [(Stmt,Exp,Stmt)]      -- match/assignment/if statement
    | SCall   Exp                        -- procedure call
    | SSeq    Stmt Stmt                  -- sequence
    | SNop                               -- dummy statement (internal)
    | SRet    Exp                        -- terminate program with exp
    | SLoop'  Stmt Stmt                  -- unrolled SLoop (internal)
    | SRet'   Exp                        -- ret with Exp eval'd
    | SVar'   Stmt                       -- scope
    deriving (Eq, Show)

infixr 1 `SSeq`

fromExp :: B.Exp -> Exp
fromExp (B.EError  _ v)   = EError  v
fromExp (B.EVar    _ id)  = EVar id
fromExp (B.EUnit   _)     = EUnit
fromExp (B.ECons   z id)  = case typec z of
                             (TData False _ _ (TUnit False), _) -> EData id EUnit
                             otherwise            -> ECons id
fromExp (B.ETuple  _ vs)  = ETuple (map fromExp vs)
fromExp (B.EFunc   _ _ us p) = EFunc (fromExp us) (fromStmt p)
fromExp (B.EFNew   _ ids f) = EFNew (fromExp ids) (fromExp f)
fromExp (B.ECall   _ f e) = ECall (fromExp f) (fromExp e)
fromExp (B.EAny    _)     = EAny
fromExp (B.EArg    _)     = EVar "_arg"
fromExp (B.EUpv    _)     = EVar "_upv"
fromExp (B.EExp    _ e)   = EExp (fromExp e)
fromExp (B.EMatch  _ e p) = EMatch (fromExp e) (fromExp p)
fromExp (B.ERefRef _ e)   = ERefRef (fromExp e)
fromExp (B.ERefDer _ e)   = ERefDer (fromExp e)
fromExp (B.ERefIni _ e)   = ERefIni (fromExp e)

-------------------------------------------------------------------------------

fromStmt :: B.Stmt -> Stmt
fromStmt (B.SData   _ _ _ _ p)       = fromStmt p
fromStmt (B.SVar    _ id _ p)        = SVar id (fromStmt p)
fromStmt (B.SCall   _ e)             = SCall (fromExp e)
fromStmt (B.SSeq    _ p1 p2)         = SSeq (fromStmt p1) (fromStmt p2)
fromStmt (B.SLoop   _ p)             = SLoop' (fromStmt p) (fromStmt p)
fromStmt (B.SRet    _ e)             = SRet (fromExp e)
fromStmt (B.SNop    _)               = SNop
fromStmt (B.SMatch  _ _ _ exp cses)  = SMatch (fromExp exp) $
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

envEval :: DescE -> DescE
envEval (e,vars) = case e of
    EVar  var -> (envRead vars var, vars)
    ETuple es -> case find isError es' of
                    Nothing  -> (ETuple es', vars')
                    Just exp -> (exp, vars')
                  where
                    isError (EError _) = True
                    isError _         = False

                    (es', vars') = f (es,vars)

                    f :: ([Exp],Vars) -> ([Exp],Vars)
                    f ((e:l),vars) = (e':l', vars'') where
                                      (e',vars')  = envEval (e,vars)
                                      (l',vars'') = f (l,vars')
                    f ([],vars)    = ([],vars)

    EMatch exp pat -> case match vars' pat exp' of
                        (Left  err,   _) -> (err, vars')
                        (Right False, _) -> (EData ["Bool","False"] EUnit, vars')
                        (Right True,  _) -> (EData ["Bool","True"]  EUnit, vars')
                      where
                        (exp',vars') = envEval (exp,vars)

    ERefRef exp -> (exp, vars)
    ERefDer exp -> envEval $ envEval (exp,vars)

    EFNew ids (EFunc _ p) -> envEval ((EFunc e' p), vars') where
                              (e',vars') = envEval (ids,vars)

    ECall f arg ->
      case (f', arg') of
        (EError x, _)                                   -> (EError x, vars)
        (_, EError x)                                   -> (EError x, vars)
        (EVar "print",  x)                              -> (traceShowId x, vars)
        (EVar "negate", EData ["Int",x] EUnit)          -> (EData ["Int",show (- (read x))] EUnit, vars)
        (EVar "+",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData ["Int",show (read x   +   read y)] EUnit, vars)
        (EVar "-",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData ["Int",show (read x   -   read y)] EUnit, vars)
        (EVar "*",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData ["Int",show (read x   *   read y)] EUnit, vars)
        (EVar "/",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData ["Int",show (read x `div` read y)] EUnit, vars)
        (EVar "rem",    ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData ["Int",show (read x `rem` read y)] EUnit, vars)
        (EVar "==",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData (bool ["Bool","False"] ["Bool","True"] (read' x == read' y)) EUnit, vars)
        (EVar "<=",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData (bool ["Bool","False"] ["Bool","True"] (read' x <= read' y)) EUnit, vars)
        (EVar "<",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (EData (bool ["Bool","False"] ["Bool","True"] (read' x < read' y))  EUnit, vars)
        (ECons id,       e)                             -> (EData id e', vars') where (e',vars') = envEval (e,vars)
        (EFunc upv p,    arg)                           -> steps (p, ("_upv",Just upv):("_arg",Just arg):vars) where
        --x                                               -> error $ show (x,f,e',vars)
      where
        (f',  vars')  = envEval (f,   vars)
        (arg',vars'') = envEval (arg, vars')

    e         -> (e, vars)

----------------------------------------------------------------------------

match :: Vars -> Exp -> Exp -> (Either Exp Bool, Vars)
match vars EAny        _ = (Right True, vars)
match vars (EVar id)   v = (Right True, envWrite vars id v)
match vars EUnit       v = (Right True, vars)
match vars (EData hrp _)
           (EData hre _) = (Right ret, vars) where
                            ret = T.isRel T.SUP (TData False hrp [] (TUnit False)) (TData False hre [] (TUnit False))
match vars (ECall (ECons hrp) l)
           (EData hre e) = (ret', vars')  where
                            v1 = T.isRel T.SUP (TData False hrp [] (TUnit False)) (TData False hre [] (TUnit False))
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
match vars (EExp x)    v = case x of
                            EError y -> (Left  $ EError y, vars')
                            e'       -> (Right $ e' == v,  vars')
                           where
                            (x',vars') = envEval (x,vars)

match vars (ERefIni x) v = match vars x v
match vars (ERefDer x) v = match vars' x' v where (x',vars') = envEval (x,vars)

match x y z = error $ show (y,z)
--err xp got = error $ "assignment does not match : expected '" ++ show xp ++
                                             --"' : found '"    ++ show got ++ "'"

----------------------------------------------------------------------------

step :: DescS -> DescS

step (SVar  id p,       vars) = (SVar' p,  (id,Nothing):vars)

step (SVar' SNop,      _:vars) = (SNop,     vars)
step (SVar' (SRet' e), _:vars) = (SRet' e,  vars)
step (SVar' p,           vars) = (SVar' p', vars') where
                                  (p',vars') = step (p,vars)

step (SCall e,          vars) = (p,        vars') where
                                  (e', vars') = envEval (e,vars)
                                  p = case e' of
                                        EError v  -> SRet e'
                                        otherwise -> SNop

step (SMatch e cses,  vars)   = case e' of
                                  EError x  -> (SRet (EError x), vars')
                                  otherwise -> toDesc $ foldl (aux e') (Right False, vars', SNop) cses
  where
    (e', vars') = envEval (e,vars)

    toDesc :: (Either Exp Bool, Vars, Stmt) -> DescS
    toDesc (_, vars, stmt) = (stmt,vars)

    aux :: Exp -> (Either Exp Bool, Vars, Stmt) -> (Stmt,Exp,Stmt) -> (Either Exp Bool, Vars, Stmt)
    aux exp all@(ret,vars0,stmt) (ds,pat,stmt') =
      case (ret,ret') of
        (Left  err,  _)            -> all
        (Right True, _)            -> all
        (Right False, Left  err)   -> (ret', vars2, SRet err)
        (Right False, Right _)     -> (ret', vars2, stmt')
      where
        (ret', vars2) = match vars1 pat exp
        vars1 = f ds vars0 where
          f SNop        vars = vars
          f (SVar id p) vars = (id,Nothing) : (f p vars)    -- TODO: maybe wrong

step (SSeq SNop     q,  vars)  = (q,           vars)
step (SSeq (SRet e) q,  vars)  = (SRet e,      vars)
step (SSeq p        q,  vars)  = (SSeq p' q,   vars') where (p',vars') = step (p,vars)

step (SLoop' SNop     q, vars) = (SLoop' q q,  vars)
step (SLoop' (SRet e) q, vars) = (SRet e,      vars)
step (SLoop' p q, vars)        = (SLoop' p' q, vars') where (p',vars') = step (p,vars)

step (SRet e, vars) = (SRet' e', vars') where
                        (e', vars') = envEval (e,vars)

step p =  error $ "step: cannot advance : " ++ (show p)

----------------------------------------------------------------------------

steps :: DescS -> DescE
steps (SRet' e, vars) = (e, vars)
steps d               = if (envRead vars "_steps") == (EData ["Int",show 1000] EUnit) then
                          (EError error_terminate, vars)
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
go' p = fst $ steps (fromStmt p, [("_steps",Just $ EData ["Int","0"] EUnit)])
