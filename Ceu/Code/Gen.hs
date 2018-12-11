module Ceu.Code.Gen where

import Debug.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data State = State { spc   :: String
                   , traps :: [Stmt All]
                   , trail :: Int
                   } -- deriving (Show)   

z :: State
z = State { spc   = ""
          , traps = []
          , trail = 0
          }

ident :: State -> State
ident g = g{ spc=(spc g)++"  " }

-------------------------------------------------------------------------------

ocmd :: State -> String -> String
ocmd g str = (spc g) ++ str ++ ";\n"

oblk :: State -> String -> String
oblk g str = (spc g) ++ "{\n" ++ str ++ (spc g) ++ "}\n"

-------------------------------------------------------------------------------

expr :: Exp ann -> String
expr (Const _ n) = show n

-------------------------------------------------------------------------------

label :: Stmt All -> String -> String
label s lbl = "CEU_LABEL_" ++ (show $ toN s) ++ "_" ++ lbl

stmt :: Stmt Source -> String
stmt p = aux (ident z) (N.add p) --(traceShowId p)

aux :: State -> Stmt All -> String
aux g (Var      _ var p)     = aux g p
aux g (Write    _ var exp)   = ocmd g $ "CEU_APP.root." ++ var ++ " = " ++ (expr exp)
aux g (AwaitExt _ "FOREVER") = ocmd g $ "return"
aux g (Seq      _ p1 p2)     = (aux g p1) ++ (aux g p2)

aux g s@(AwaitExt _ ext) =
    (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].evt" ++ " = " ++ evt) ++
    (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].lbl" ++ " = " ++ lbl) ++
    (ocmd g $ "return") ++
    (ocmd z $ "case " ++ lbl)
    where
        trl = show $ trail g
        evt = "CEU_INPUT_" ++ ext
        lbl = label s ("AwaitExt_" ++ ext)

aux g (EmitExt  _ ext exp) =
    ocmd g $ "CEU_OUTPUT_" ++ ext ++ "(" ++ exp' ++ ")"
    where
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr v

aux g (If _ exp p1 p2) =
    (spc g) ++ "if (" ++ (expr exp) ++ ")\n" ++
                    oblk g (aux (ident g) p1) ++
    (spc g) ++ "else\n" ++
                    oblk g (aux (ident g) p2)

aux g s@(Trap _ p) =
    ocmd z $ (aux g' p) ++ "case " ++ (label s "Trap") ++ ":"
    where
        g' = g{ traps = s:(traps g) }

aux g (Escape _ k) = ocmd g $ "CEU_GOTO(" ++ (label ((traps g)!!k) "Trap") ++ ")"
