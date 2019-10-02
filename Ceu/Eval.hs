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

type DescS = (Vars, Stmt)
type DescE = (Vars, Exp)

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
fromExp (B.ECons   z id)  = case fst $ typec z of
                             TData False _ _ -> EData id EUnit
                             otherwise       -> ECons id
fromExp (B.ETuple  _ vs)  = ETuple (map fromExp vs)
fromExp (B.EFunc   _ _ us p) = EFunc (fromExp us) (fromStmt p)
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
fromStmt (B.SData   _ _ _ _ _ _ p)   = fromStmt p
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
envEval (vars,e) = case e of
    EVar  var -> (vars, envRead vars var)
    ETuple es -> case find isError es' of
                    Nothing  -> (vars', ETuple es')
                    Just exp -> (vars', exp)
                  where
                    isError (EError _) = True
                    isError _          = False

                    (vars',es') = f (vars, es)

                    f :: (Vars,[Exp]) -> (Vars,[Exp])
                    f (vars,(e:l)) = (vars'', e':l') where
                                      (vars', e') = envEval (vars,e)
                                      (vars'',l') = f (vars',l)
                    f (vars,[])    = (vars,[])

    EMatch exp pat -> case match vars' pat exp' of
                        (vars'', Left  err)   -> (vars'', err)
                        (vars'', Right False) -> (vars'', EData ["Bool","False"] EUnit)
                        (vars'', Right True)  -> (vars'', EData ["Bool","True"]  EUnit)
                      where
                        (vars',exp') = envEval (vars, exp)

    ERefRef exp -> (vars, exp)
    ERefDer exp -> envEval $ envEval (vars, exp)

    EFunc upv p -> (vars', EFunc upv' p) where (vars',upv') = envEval (vars,upv)

    ECall f arg ->
      case (f', arg') of
        (EError x, _)                                   -> (vars'', EError x)
        (_, EError x)                                   -> (vars'', EError x)
        (EVar "print",  x)                              -> (vars'', traceShowId x)
        (EVar "negate", EData ["Int",x] EUnit)          -> (vars'', EData ["Int",show (- (read x))] EUnit)
        (EVar "+",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData ["Int",show (read x   +   read y)] EUnit)
        (EVar "-",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData ["Int",show (read x   -   read y)] EUnit)
        (EVar "*",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData ["Int",show (read x   *   read y)] EUnit)
        (EVar "/",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData ["Int",show (read x `div` read y)] EUnit)
        (EVar "rem",    ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData ["Int",show (read x `rem` read y)] EUnit)
        (EVar "==",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData (bool ["Bool","False"] ["Bool","True"] (read' x == read' y)) EUnit)
        (EVar "<=",     ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData (bool ["Bool","False"] ["Bool","True"] (read' x <= read' y)) EUnit)
        (EVar "<",      ETuple [EData ["Int",x] EUnit,
                                EData ["Int",y] EUnit]) -> (vars'', EData (bool ["Bool","False"] ["Bool","True"] (read' x < read' y))  EUnit)
        (ECons id,       e)                             -> (vars'', EData id e)
        (EFunc upv p,    arg)                           -> (vars''', e) where
                                                            (_:_:vars''', e) = steps (("_upv",Just upv):("_arg",Just arg):vars'', p)
        --(x,y) -> error $ show (x,arg)
      where
        (vars',  f')   = envEval (vars,   f)
        (vars'', arg') = envEval (vars', arg)


    e         -> (vars, e)

----------------------------------------------------------------------------

match :: Vars -> Exp -> Exp -> (Vars, Either Exp Bool)
match vars EAny        _ = (vars, Right True)
match vars (EVar id)   v = (envWrite vars id v, Right True)
match vars EUnit       v = (vars, Right True)
match vars (EData hrp _)
           (EData hre _) = (vars, Right ret) where
                            ret = T.isRel T.SUP (TData False hrp []) (TData False hre [])
match vars (ECall (ECons hrp) l)
           (EData hre e) = (vars', ret')  where
                            v1 = T.isRel T.SUP (TData False hrp []) (TData False hre [])
                            (vars', ret2) = match vars l e
                            ret' = case ret2 of
                              Left  x  -> Left  x
                              Right v2 -> Right (v1 && v2)
match vars (ETuple ps)
           (ETuple es)   = foldr
                            (\(loc,e) (vars1,b1) ->
                              if b1/=(Right True) then (vars1,b1) else
                                match vars1 loc e)
                            (vars, Right True)
                            (zip ps es)
match vars (EExp x)    v = case x' of
                            EError y -> (vars', Left  $ EError y)
                            e'       -> (vars', Right $ e' == v)
                           where
                            (vars',x') = envEval (vars,x)

match vars (ERefIni x) v = match vars x v
match vars (ERefDer x) v = match vars' x' v where (vars',x') = envEval (vars,x)

match x y z = error $ show (y,z)
--err xp got = error $ "assignment does not match : expected '" ++ show xp ++
                                             --"' : found '"    ++ show got ++ "'"

----------------------------------------------------------------------------

step :: DescS -> DescS

step (  vars, SVar  id p)      = ((id,Nothing):vars,  SVar' p)

step (_:vars, SVar' SNop)      = (vars,  SNop)
step (_:vars, SVar' (SRet' e)) = (vars,  SRet' e)
step (  vars, SVar' p)         = (vars', SVar' p') where (vars',p') = step (vars,p)

step (vars, SCall e)           = (vars', p) where
                                  (vars', e') = envEval (vars,e)
                                  p = case e' of
                                        EError v  -> SRet e'
                                        otherwise -> SNop

step (vars, SMatch e cses)     = case e' of
                                  EError x  -> (vars', SRet (EError x))
                                  otherwise -> toDesc $ foldl (aux e') (Right False, vars', SNop) cses
  where
    (vars', e') = envEval (vars,e)

    toDesc :: (Either Exp Bool, Vars, Stmt) -> DescS
    toDesc (_, vars, stmt) = (vars,stmt)

    aux :: Exp -> (Either Exp Bool, Vars, Stmt) -> (Stmt,Exp,Stmt) -> (Either Exp Bool, Vars, Stmt)
    aux exp all@(ret,vars0,stmt) (ds,pat,stmt') =
      case (ret,ret') of
        (Left  err,  _)            -> all
        (Right True, _)            -> all
        (Right False, Left  err)   -> (ret', vars2, SRet err)
        (Right False, Right _)     -> (ret', vars2, stmt')
      where
        (vars2, ret') = match vars1 pat exp
        vars1 = f ds vars0 where
          f SNop        vars = vars
          f (SVar id p) vars = (id,Nothing) : (f p vars)    -- TODO: maybe wrong

step (vars, SSeq   SNop      q) = (vars,  q)
step (vars, SSeq   (SRet' e) q) = (vars,  SRet' e)
step (vars, SSeq   p         q) = (vars', SSeq p' q) where (vars',p') = step (vars,p)

step (vars, SLoop' SNop      q) = (vars,  SLoop' q q)
step (vars, SLoop' (SRet' e) q) = (vars,  SRet' e)
step (vars, SLoop' p         q) = (vars', SLoop' p' q) where (vars',p') = step (vars,p)

step (vars, SRet e) = (vars', SRet' e') where (vars',e') = envEval (vars,e)

step p =  error $ "step: cannot advance : " ++ (show p)

----------------------------------------------------------------------------

steps :: DescS -> DescE
steps (vars, SRet' e) = (vars, e)
steps d               = if (envRead vars "_steps") == (EData ["Int",show 10000] EUnit) then
                          (vars, EError error_terminate)
                        else
                          steps (step d') where
                            (vars,s)              = d
                            d'                    = (vars',s)
                            vars'                 = envWrite vars "_steps" (EData ["Int", show (read v+1)] EUnit)
                            EData ["Int",v] EUnit = envRead  vars "_steps"

go :: B.Stmt -> Exp
go p = case T.go p of
    ([], p) -> go' p
    (es, _) -> error $ "compile error : " ++ show es

go' :: B.Stmt -> Exp
go' p = snd $ steps ([("_steps",Just $ EData ["Int","0"] EUnit)], fromStmt p)
