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
                   , vars  :: [Stmt All]
                   , trail :: Int
                   } -- deriving (Show)   

z :: State
z = State { spc   = ""
          , vars  = []
          , traps = []
          , trail = 0
          }

gind :: State -> State
gind g = g{ spc=(spc g)++"  " }

-------------------------------------------------------------------------------

ocmd :: State -> String -> String
ocmd g str = (spc g) ++ str ++ ";\n"

oblk :: State -> String -> String
oblk g str = (spc g) ++ "{\n" ++ str ++ (spc g) ++ "}\n"

oln :: Stmt All -> String
oln p = "#line " ++ (show ln) ++ ['"'] ++ file ++ ['"'] ++ comm ++ "\n"
    where
        Just (file,ln,_) = toSource p
        comm             = " // " ++ (toWord p)

-------------------------------------------------------------------------------

expr :: Exp ann -> String
expr (Const _ n) = show n

-------------------------------------------------------------------------------

label :: Stmt All -> String -> String
label s lbl = "CEU_LABEL_" ++ (show $ toN s) ++ "_" ++ lbl

stmt :: Stmt Source -> String
stmt p = snd $ aux (gind z) (N.add p) --(traceShowId p)

aux :: State -> Stmt All -> (Int,String)

aux g s@(Nop   _)         = (1, oln s)
aux g s@(Var   _ var p)   = aux g{vars=s:(vars g)} p
aux g s@(Write _ var exp) = (1, oln s ++ (ocmd g $ "CEU_APP.root." ++ var ++ " = " ++ (expr exp)))

aux g (Seq _ p1 p2) = (max t1 t2, p1'++p2')
    where
        (t1,p1') = aux g p1
        (t2,p2') = aux g p2

aux g s@(AwaitInp _ "FOREVER") = (1, oln s ++ ocmd g "return")
aux g s@(AwaitInp _ ext) = (1, p')
    where
        p' = oln s ++
             (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].evt" ++ " = " ++ evt) ++
             (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].lbl" ++ " = " ++ lbl) ++
             (ocmd g $ "return") ++
             (ocmd z $ "case " ++ lbl)
        trl = show $ trail g
        evt = "CEU_INPUT_" ++ ext
        lbl = label s ("AwaitInp_" ++ ext)

aux g s@(EmitExt _ ext exp) = (1, p')
    where
        p' = oln s ++ (ocmd g $ "ceu_callback_output_" ++ ext ++ "(" ++ exp' ++ ")")
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr v

aux g s@(If _ exp p1 p2) = (max t1 t2, p')
    where
        (t1,p1') = aux (gind g) p1
        (t2,p2') = aux (gind g) p2
        p' = oln s ++
             spc g ++ "if (" ++ expr exp ++ ")\n" ++ oblk g p1' ++
             spc g ++ "else\n" ++ oblk g p2'

aux g s@(Loop _ p) = (t, p'')
    where
        p'' = oln s ++ spc g ++ "for (;;)\n" ++ (oblk g p')
        (t, p') = aux (gind g) p

aux g s@(Par _ p1 p2) = (t1+t2, p')
    where
        p' = oln s ++ oblk g p1' ++ oblk g p2'
        (t1,p1') = aux (gind g) p1
        (t2,p2') = aux (gind g{trail=(trail g)+t1}) p2

aux g s@(Trap _ p) = (t, p'')
    where
        p'' = oln s ++ (ocmd z $ oblk g p' ++ "case " ++ (label s "Trap") ++ ":")
        (t, p') = aux g' p
        g' = gind g{ traps = s:(traps g) }

aux g s@(Escape _ k) = (1, oln s ++
                           (ocmd g $ "CEU_GOTO(" ++ (label ((traps g)!!k) "Trap") ++ ")"))
