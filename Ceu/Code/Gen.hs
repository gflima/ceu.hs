module Ceu.Code.Gen where

import Debug.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data Down = Down { spc     :: String
                 , traps   :: [Stmt All]
                 , trail_0 :: Int
                 } -- deriving (Show)

dnz :: Down
dnz = Down { spc     = ""
           , traps   = []
           , trail_0 = 0
           }

dn_spc :: Down -> Down
dn_spc g = g{ spc=(spc g)++"  " }

-------------------------------------------------------------------------------

data Up = Up { labels   :: [String]
             , inps     :: [String]
             , vars     :: [String]
             , trails_n :: Int
             , code     :: String
             }
    deriving Show

upz :: Up
upz = Up { labels   = []
         , inps     = []
         , vars     = []
         , trails_n = 1
         , code     = ""
         }

up_union_max :: Up -> Up -> Up
up_union_max u1 u2 = upz { labels   = (labels u1) ++ (labels u2)
                         , trails_n = max (trails_n u1) (trails_n u2)
                         }

up_union_sum :: Up -> Up -> Up
up_union_sum u1 u2 = upz { labels   = (labels u1) ++ (labels u2)
                         , trails_n = (trails_n u1) + (trails_n u2)
                         }

-------------------------------------------------------------------------------

ocmd :: Down -> String -> String
ocmd g str = (spc g) ++ str ++ ";\n"

oblk :: Down -> String -> String
oblk g str = (spc g) ++ "{\n" ++ str ++ (spc g) ++ "}\n"

oln :: Stmt All -> String
oln p = "#line " ++ (show ln) ++ ['"'] ++ file ++ ['"'] ++ comm ++ "\n"
    where
        Just (file,ln,_) = toSource p
        comm             = " // " ++ (toWord p)

-------------------------------------------------------------------------------

expr :: Exp ann -> String
expr (Const _ n)  = show n
expr (Read  _ id) = if id == "_INPUT" then "_CEU_INPUT" else "CEU_APP.root."++id

-------------------------------------------------------------------------------

label :: Stmt All -> String -> String
label s lbl = "CEU_LABEL_" ++ (show $ toN s) ++ "_" ++ lbl

stmt :: Stmt Source -> [(String,String)]
stmt p = [ ("CEU_INPS",   concat $ map (\inp->"    CEU_INPUT_"++inp++",\n") $ inps up)
         , ("CEU_LABELS", concat$labels up)
         , ("CEU_VARS",   concat $ map (\var->"    int "++var++";\n") $ vars up)
         , ("CEU_CODES",  code up)
         ] where
    up = aux (dn_spc dnz) (N.add p)

aux :: Down -> Stmt All -> Up

aux g s@(Nop   _)        = upz { code=(oln s) }
aux g s@(Halt  _)        = upz { code=(oln s ++ ocmd g "return 0") }
aux g s@(Var   _ id p)   = p' { vars=id:(vars p') } where p'=(aux g p)
aux g s@(Inp   _ id p)   = p' { inps=id:(inps p') } where p'=(aux g p)
aux g s@(Out   _ id p)   = aux g p
aux g s@(Write _ var exp) = upz { code=src }
    where
        src = (oln s ++ (ocmd g $ "CEU_APP.root." ++ var ++ " = " ++ (expr exp)))

aux g (Seq _ p1 p2) = (up_union_max p1' p2') { code=(code p1')++(code p2') }
    where
        p1' = aux g p1
        p2' = aux g p2

aux g s@(AwaitInp _ ext) = upz { labels=[lbl], code=src }
    where
        src = oln s ++
             (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].evt.id" ++ " = " ++ evt) ++
             (ocmd g $ "_ceu_mem->_trails[" ++ trl ++ "].lbl" ++ " = " ++ lbl) ++
             (ocmd g $ "return 0") ++
             (ocmd dnz $ "case " ++ lbl ++ ":")
        trl = show $ trail_0 g
        evt = "CEU_INPUT_" ++ ext
        lbl = label s ("AwaitInp_" ++ ext)

aux g s@(EmitExt _ ext exp) = upz { code=src }
    where
        src = oln s ++ (ocmd g $ "ceu_callback_output_" ++ ext ++ "(" ++ exp' ++ ")")
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr v

aux g s@(If _ exp p1 p2) = (up_union_max p1' p2') { code=src }
    where
        p1' = aux (dn_spc g) p1
        p2' = aux (dn_spc g) p2
        src = oln s ++
              spc g ++ "if (" ++ expr exp ++ ")\n" ++ oblk g (code p1') ++
              spc g ++ "else\n" ++ oblk g (code p2')

aux g s@(Loop _ p) = p' { code=src }
    where
        p'  = aux (dn_spc g) p
        src = oln s ++ spc g ++ "for (;;)\n" ++ (oblk g (code p'))

aux g s@(Par _ p1 p2) = (up_union_sum p1' p2') { code=src }
    where
        p1' = aux (dn_spc g) p1
        p2' = aux (dn_spc g{trail_0=(trail_0 g)+(trails_n p1')}) p2
        src = "TODO" --oln s ++ oblk g (code p1') ++ oblk g (code p2')

aux g s@(Trap _ p) = p' { labels=lbl:(labels p'), code=src }
    where
        p'  = aux g' p
        src = oln s ++ (ocmd dnz $ oblk g (code p') ++ "case " ++ lbl ++ ":")
        g'  = dn_spc g{ traps = s:(traps g) }
        lbl = label s "Trap"

aux g s@(Escape _ k) = upz { code=src }
    where
        src = oln s ++ (ocmd g $ "CEU_GOTO(" ++ (label ((traps g)!!k) "Trap") ++ ")")
