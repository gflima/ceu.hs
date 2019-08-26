module Ceu.Grammar.Basic where

import Data.Bool                      (bool)
import Data.List                      (intercalate)

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann                (Ann, HasAnn(..), annz)
import Ceu.Grammar.Constraints as Cs  (Map, cz)
import Ceu.Grammar.Type        as T   (TypeC, Type(..), show', hier2str)

-------------------------------------------------------------------------------

data Exp
    = EError  Ann Int
    | EVar    Ann ID_Var         -- a ; xs
    | EUnit   Ann                -- ()
    | ECons   Ann ID_Data_Hier   -- Bool.True ; Int.1 ; Tree.Node
    | EField  Ann ID_Data_Hier String -- List.Cons._1 // Student.age
    | ETuple  Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc   Ann TypeC Exp Stmt -- function implementation
    | ECall   Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    | EAny    Ann
    | EArg    Ann
    | EUpv    Ann
    | EExp    Ann Exp
    | EMatch  Ann Exp Exp
    | ERefRef Ann Exp            -- &a    // get reference of expression
    | ERefDer Ann Exp            -- *&a   // dereference expression
    | ERefIni Ann Exp            -- a =   // bind reference
    deriving (Eq, Show)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (EError  z _)   = z
    getAnn (EVar    z _)   = z
    getAnn (EUnit   z)     = z
    getAnn (ECons   z _)   = z
    getAnn (EField  z _ _) = z
    getAnn (ETuple  z _)   = z
    getAnn (EFunc   z _ _ _) = z
    getAnn (ECall   z _ _) = z
    getAnn (EAny    z)     = z
    getAnn (EArg    z)     = z
    getAnn (EUpv    z)     = z
    getAnn (EExp    z _)   = z
    getAnn (EMatch  z _ _) = z
    getAnn (ERefRef z _)   = z
    getAnn (ERefDer z _)   = z
    getAnn (ERefIni z _)   = z

-------------------------------------------------------------------------------

data Stmt
    = SClass  Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class declaration
    | SInst   Ann ID_Class TypeC  [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class instance
    | SData   Ann Type (Maybe [String]) Type Cs.Map Bool Stmt  -- new type declaration
    | SVar    Ann ID_Var TypeC Stmt            -- variable declaration
    | SMatch  Ann Bool Bool Exp [(Stmt,Exp,Stmt)]   -- match/assignment/if statement
    | SCall   Ann Exp                          -- call function
    | SSeq    Ann Stmt Stmt                    -- sequence
    | SLoop   Ann Stmt                         -- infinite loop
    | SRet    Ann Exp                          -- terminate program with SRet
    | SNop    Ann                              -- dummy statement (internal)
    deriving (Eq, Show)

-------------------------------------------------------------------------------

data EnvType = EnvGlobal | EnvNonLocal | EnvLocal
  deriving Show

type Envs = [[Stmt]]  -- [ [bodyZ],[argsZ], ..., [bodyA],[argsA] ]

envsAdd :: Envs -> Stmt -> Envs
envsAdd (x:xs) s = (s:x) : xs

-------------------------------------------------------------------------------

isClass id1 (SClass _ id2 _ _ _) = (id1 == id2)
isClass _   _                    = False

isData  hr1 (SData  _ (TData False hr2 _) _ _ _ _ _) = (hr1' == hier2str hr2) where
                                                        hr1' = bool hr1 "Int" (take 4 hr1 == "Int.")
isData  _   _                                        = False

isVar   id1 (SVar   _ id2 _ _)   = (id1 == id2)
isVar   _   _                    = False

-------------------------------------------------------------------------------

rep spc = replicate spc ' '

show_stmt :: Int -> Stmt -> String
--show_stmt spc (SClass _ (id,_) _ _ p) = rep spc ++ "class "  ++ id ++ "\n" ++ show_stmt spc p
--show_stmt spc (SInst  _ (id,_) _ p)   = rep spc ++ "inst "   ++ id ++ "\n" ++ show_stmt spc p
show_stmt spc (SData _ (TData False id _) _ _ _ _ p) = rep spc ++ "data "   ++ intercalate "." id ++ "\n" ++ show_stmt spc p
show_stmt spc (SVar _ id (tp,_) p)     = rep spc ++ "var "    ++ id ++ ": " ++ T.show' tp ++ "\n" ++ show_stmt spc p
show_stmt spc (SCall _ e)              = rep spc ++ "call " ++ show_exp spc e
show_stmt spc (SRet _ e)               = rep spc ++ "return " ++ show_exp spc e
show_stmt spc (SSeq _ p1 p2)           = show_stmt spc p1 ++ "\n" ++ show_stmt spc p2
  --rep spc ++ "--\n" ++ show_stmt (spc+4) p1 ++ rep spc ++ "--\n" ++ show_stmt (spc+4) p2
show_stmt spc (SMatch _ _ False exp [(_,pt,st)])
                                       = rep spc ++ "set " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
show_stmt spc (SMatch _ _ True  exp ((ds,pt,st):_))
                                       = rep spc ++ "set! " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
show_stmt spc (SMatch _ _ chk exp cses)  = rep spc ++ "match " ++ show_exp spc exp ++ " with\n" ++ (concatMap f cses)
                                         where
                                          f (ds,pt,st) = rep (spc+4) ++ show_exp (spc+4) pt ++
                                                          " { " ++ show_stmt 0 ds ++ " } then\n" ++
                                                          show_stmt (spc+8) st ++ "\n"
show_stmt spc (SNop _)                 = rep spc ++ "nop"
show_stmt spc p = error $ show p

show_exp :: Int -> Exp -> String
show_exp spc (EAny   _)           = "_"
show_exp spc (EUnit  _)           = "()"
show_exp spc (EError _ n)         = "error " ++ show n
show_exp spc (ECons  _ ["Int",n]) = n
show_exp spc (ECons  _ id)        = hier2str id
show_exp spc (EVar   _ id)        = id
show_exp spc (EArg   _)           = "arg"
show_exp spc (EUpv   _)           = "upv"
show_exp spc (ETuple _ es)        = "(" ++ intercalate "," (map (show_exp spc) es) ++ ")"
show_exp spc (EFunc  _ _ _ p)     = "func" ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (ECall  _ e1 e2)     = "call" ++ " " ++ show_exp spc e1 ++ " " ++ show_exp spc e2
show_exp spc (EMatch _ exp pat)   = "match" ++ " " ++ show_exp spc exp ++ " with " ++ show_exp spc pat
show_exp spc (EExp   _ exp)       = show_exp spc exp
show_exp spc (ERefRef _ exp)      = "ref " ++ show_exp spc exp
show_exp spc (ERefIni _ exp)      = show_exp spc exp
show_exp spc (ERefDer _ exp)      = "acc " ++ show_exp spc exp
show_exp spc e                    = error $ show e

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Stmt -> Stmt
map_stmt f@(fs,_,ft) (SClass z id ctr ifc p)     = fs (SClass z id ctr ifc' (map_stmt f p))
                                                    where ifc' = map (\(x,y,tp,z)->(x,y,ft tp,z)) ifc
map_stmt f@(fs,_,ft) (SInst  z cls tp imp p)     = fs (SInst  z cls tp imp' (map_stmt f p))
                                                    where imp' = map (\(x,y,tp,z)->(x,y,ft tp,z)) imp
map_stmt f@(fs,_,ft) (SData  z tdat nms flds ctrs abs p) = fs (SData z tdat nms flds ctrs abs (map_stmt f p))
map_stmt f@(fs,_,ft) (SVar   z id tp p)          = fs (SVar   z id (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (SMatch z ini b exp cses)   = fs (SMatch z ini b (map_exp f exp) (map (\(ds,pt,st) -> (map_stmt f ds, map_exp f pt, map_stmt f st)) cses))
map_stmt f@(fs,_,_)  (SCall z exp)               = fs (SCall z (map_exp f exp))
map_stmt f@(fs,_,_)  (SSeq   z p1 p2)            = fs (SSeq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (SLoop  z p)                = fs (SLoop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (SRet   z exp)              = fs (SRet   z (map_exp f exp))
map_stmt f@(fs,_,_)  (SNop   z)                  = fs (SNop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Exp -> Exp
map_exp f@(_,fe,_)  (ECons  z id)    = fe (ECons  z id)
map_exp f@(_,fe,_)  (ETuple z es)    = fe (ETuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (EFunc  z tp upv p) = fe (EFunc  z (ft tp) (map_exp f upv) (map_stmt f p))
map_exp f@(_,fe,_)  (ECall  z e1 e2) = fe (ECall  z (map_exp f e1) (map_exp f e2))
map_exp f@(_,fe,_)  exp              = fe exp

--  class Equalable a where
--      eq :: a -> a -> Bool
--
--  instance Equalable X where
--      eq :: X -> X -> Bool
--      eq a b = ...
--
--  instance Equalable Int where
--      eq :: Int -> Int -> Bool
--      eq a b = <primitive>
--
--  eq 10 20    :: eq Int Int
--
-- To resolve call to `eq`:
--  * find associated `func`:
--      * top-level funcs
--      * class declarations
--      ! only one is allowed in the whole program
--      * in either case, check if type matches
--  * if found class:
--      * instantiate class variable `a` against call `eq 10 20`, resolving to `Int`
--          ! must find `instance Equable Int`
--
-- Expected layout of SInst.imp:
--  (SVar _ "f" tp
--    (SSeq _
--      (Write _ (LVar "f") (EFunc ...))   -- or (SNop _) // no implementation
--      (SVar _ "g" tp                     -- or (SNop _) // eof
--        ...

sSeq a b = SSeq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (SClass z _ _ _ _)   = z
    getAnn (SInst  z _ _ _ _)   = z
    getAnn (SData  z _ _ _ _ _ _) = z
    getAnn (SVar   z _ _ _)     = z
    getAnn (SMatch z _ _ _ _)   = z
    getAnn (SCall z _)          = z
    getAnn (SSeq   z _ _)       = z
    getAnn (SLoop  z _)         = z
    getAnn (SRet   z _)         = z
    getAnn (SNop   z)           = z

prelude z p = (SData z (TData False ["Int"]          []) Nothing TUnit cz False
              (SData z (TData False ["Bool"]         []) Nothing TUnit cz True
              (SData z (TData False ["Bool","True"]  []) Nothing TUnit cz False
              (SData z (TData False ["Bool","False"] []) Nothing TUnit cz False p))))
