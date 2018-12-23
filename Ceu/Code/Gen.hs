module Ceu.Code.Gen where

import Debug.Trace
import Data.Maybe
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data Down = Down { spc     :: String
                 , traps   :: [Stmt All]
                 , trail_0 :: Int
                 , vars_dn :: [(ID_Var,Int)]
                 , evts_dn :: [(ID_Evt,Int)]
                 } -- deriving (Show)

dnz :: Down
dnz = Down { spc     = ""
           , traps   = []
           , trail_0 = 0
           , vars_dn = []
           , evts_dn = []
           }

dn_spc :: Down -> Down
dn_spc g = g{ spc=(spc g)++"  " }

-------------------------------------------------------------------------------

data Up = Up { inps     :: [String]
             , vars_up  :: [String]
             , evts_up  :: [String]
             , trails_n :: Int
             , code_bef :: String
             , code_brk :: Maybe String
             , code_aft :: String
             , labels   :: [String]
             }
    deriving Show

upz :: Up
upz = Up { inps     = []
         , vars_up  = []
         , evts_up  = []
         , trails_n = 1
         , code_bef = ""
         , code_brk = Nothing
         , code_aft = ""
         , labels   = []
         }

up_union :: Up -> Up -> Up
up_union u1 u2 = upz { inps     = (inps    u1) ++ (inps    u2)
                     , vars_up  = (vars_up u1) ++ (vars_up u2)
                     , evts_up  = (evts_up u1) ++ (evts_up u2)
                     , code_bef = ""
                     , code_brk = Nothing
                     , code_aft = ""
                     , labels   = []
                     }

up_copy :: Up -> Up
up_copy up = up_union_max up upz

up_union_max :: Up -> Up -> Up
up_union_max u1 u2 = (up_union u1 u2) { trails_n = max (trails_n u1) (trails_n u2) }

up_union_sum :: Up -> Up -> Up
up_union_sum u1 u2 = (up_union u1 u2) { trails_n = (trails_n u1) + (trails_n u2) }

-------------------------------------------------------------------------------

ocmd :: Down -> String -> String
ocmd g str = (spc g) ++ str ++ ";\n"

oblk :: Down -> String -> String
oblk g str = (spc g) ++ "{\n" ++ str ++ (spc g) ++ "}\n"

oln :: Stmt All -> String
oln p = "//#line " ++ (show ln) ++ " \"" ++ file ++ "\" " ++ comm ++ "\n"
    where
        Just (file,ln,_) = toSource p
        comm             = "// " ++ (toWord p)

odcl :: String -> String
odcl lbl = "int " ++ lbl ++ " (tceu_trl* _ceu_trl);\n\n"

olbl :: String -> String -> String
olbl lbl src = "int " ++ lbl ++ " (tceu_trl* _ceu_trl) " ++
                 oblk dnz src ++ "\n"

ocallret :: Down -> String -> String
ocallret g lbl = oblk g src
    where
        src = (ocmd g "int __ceu_ret = " ++ lbl ++ "(...)") ++
              (ocmd g "if (__ceu_ret != 0)")

-------------------------------------------------------------------------------

getID :: [(String,Int)] -> String -> String
getID ((v1,n):l) v2 | v1==v2    = v1++"__"++(show n)
                    | otherwise = getID l v2

expr :: [(ID_Var,Int)] -> Exp ann -> String
expr vars (Const _ n)     = show n
expr vars (Read  _ id)    = if id == "_INPUT" then "_CEU_INPUT" else
                                "CEU_APP.root."++(getID vars id)
expr vars (Equ   _ e1 e2) = (expr vars e1) ++ " == " ++ (expr vars e2)
expr vars (Add   _ e1 e2) = (expr vars e1) ++ " + "  ++ (expr vars e2)

-------------------------------------------------------------------------------

label :: Stmt All -> String -> String
label s lbl = "CEU_LABEL_" ++ (show $ toN s) ++ "_" ++ lbl

stmt :: Stmt Source -> [(String,String)]
stmt p = [ ("CEU_TRAILS_N", show $ trails_n up)
         , ("CEU_INPS",     concat $ map (\inp->"    CEU_INPUT_"++inp++",\n") $ inps    up)
         , ("CEU_EVTS",     concat $ map (\evt->"    CEU_EVENT_"++evt++",\n") $ evts_up up)
         , ("CEU_VARS",     concat $ map (\var->"    int "++var++";\n")       $ vars_up up)
         , ("CEU_LABELS",   concat $ labels up ++ root2 ++ root1 )
         ] where
    up    = aux (dn_spc dnz) (N.add $ traceShowId p)
    root1 = [ olbl "CEU_LABEL_ROOT" (code_bef up) ]
    root2 = case code_brk up of
                Nothing  -> []
                Just lbl -> [ olbl lbl (code_aft up) ]

-------------------------------------------------------------------------------

aux :: Down -> Stmt All -> Up

aux g s@(Nop   _)        = upz { code_bef=(oln s) }
aux g s@(Halt  _)        = upz { code_bef=(oln s ++ ocmd g "return 0") }
aux g s@(Inp   _ id p)   = p' { inps=id:(inps p') } where p'=(aux g p)
aux g s@(Out   _ id p)   = aux g p

-------------------------------------------------------------------------------

aux g s@(Evt _ id p) = p' { evts_up=(id++"__"++(show$toN s)):(evts_up p') }
    where
        p' = aux g' p
        g' = g{ evts_dn = (id,toN s):(evts_dn g) }

aux g s@(Var _ id p) = p' { vars_up=(id++"__"++(show$toN s)):(vars_up p') }
    where
        p' = aux g' p
        g' = g{ vars_dn = (id,toN s):(vars_dn g) }

aux g s@(Write _ var exp) = upz { code_bef=src }
    where
        src = (oln s ++ (ocmd g $ "CEU_APP.root." ++ (getID vars var) ++ " = " ++ (expr vars exp)))
        vars = vars_dn g

-------------------------------------------------------------------------------

aux g s@(AwaitInp _ ext) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln s ++
              (ocmd g $ "_ceu_trl->evt.id = " ++ evt) ++
              (ocmd g $ "_ceu_trl->lbl    = " ++ lbl) ++
              (ocmd g $ "return 0")
        trl = show $ trail_0 g
        evt = "CEU_INPUT_" ++ ext
        lbl = label s ("AwaitInp_" ++ ext)

aux g s@(AwaitEvt _ evt) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln s ++
             (ocmd g $ "_ceu_trl->evt.id = " ++ id') ++
             (ocmd g $ "_ceu_trl->lbl    = " ++ lbl)
        trl = show $ trail_0 g
        id' = "CEU_EVENT_" ++ (getID (evts_dn g) evt)
        lbl = label s ("AwaitEvt_" ++ evt)

-------------------------------------------------------------------------------

aux g s@(EmitExt _ ext exp) = upz { code_bef=src }
    where
        src = oln s ++ (ocmd g $ "ceu_callback_output_" ++ ext ++ "(" ++ exp' ++ ")")
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr (vars_dn g) v

aux g s@(EmitEvt _ evt) = upz { code_bef=emt, code_brk=(Just lbl) }
    where
        emt = oblk g $
              (ocmd g' $ "tceu_evt   __ceu_evt   = {" ++ id' ++ ",{NULL}}") ++
              (ocmd g' $ "tceu_range __ceu_range = { &CEU_APP.root._mem, 0, CEU_TRAILS_N-1 }") ++
-- TODO: emit scope
              (ocmd g' $ "_ceu_nxt->evt      = __ceu_evt") ++
              (ocmd g' $ "_ceu_nxt->range    = __ceu_range") ++
              (ocmd g' $ "_ceu_nxt->params_n = 0") ++
              (ocmd g' $ "return 1")
        id' = "CEU_EVENT_" ++ (getID (evts_dn g) evt)
        g'  = dn_spc g
        lbl = label s ("EmitEvt_" ++ evt)

-------------------------------------------------------------------------------

aux g s@(Seq _ p1 p2) = (up_union_max p1' p2') {
                        code_bef = oln s ++ bef,
                        --code_bef = bef,
                        code_brk = brk,
                        code_aft = aft,
                        labels   = lbls ++ labels p2' ++ labels p1'
                      }
    where
        p1' = aux g p1
        p2' = aux g p2

        bef1 = code_bef p1'
        bef2 = code_bef p2'
        brk1 = code_brk p1'
        brk2 = code_brk p2'
        aft1 = code_aft p1'
        aft2 = code_aft p2'

        bef  = bef1 ++ bef'
        bef' = if isNothing brk1 then bef2 else ""

        brk  = if isJust brk2 then brk2 else if isJust brk1 then brk1 else Nothing

        aft  = aft' ++ aft2
        aft' = if isJust brk2 || isNothing brk1 then "" else aft1++bef2

        lbls = if not (isJust brk1 && isJust brk2) then [] else
                [ olbl (fromJust brk1) (aft1 ++ bef2) ]

-------------------------------------------------------------------------------

aux g s@(If _ exp p1 p2) = (up_union_max p1' p2') {
                            code_bef = bef,
                            code_brk = Just lbl,
                            labels   = lbls1++lbls2 ++ labels p2' ++ labels p1'
                           }
    where
        p1' = aux (dn_spc g) p1
        p2' = aux (dn_spc g) p2
        bef = oln s ++
              spc g ++ "if (" ++ expr (vars_dn g) exp ++ ")\n" ++ oblk g bef1 ++
              spc g ++ "else\n" ++ oblk g bef2

        brk1 = code_brk p1'
        brk2 = code_brk p2'

        bef1 = (code_bef p1') ++ if isNothing brk1 then join else ""
        bef2 = (code_bef p2') ++ if isNothing brk2 then join else ""

        join = ocmd g $ "return " ++ lbl ++ "(_ceu_trl)"
        lbl  = label s "If_Join"

        lbls1 = if isNothing brk1 then [] else
                    [ olbl (fromJust brk1) $ (code_aft p1') ++ join ]
        lbls2 = if isNothing brk2 then [] else
                    [ olbl (fromJust brk2) $ (code_aft p2') ++ join ]

-------------------------------------------------------------------------------

aux g s@(Loop _ p) = (up_copy p') {
                        code_bef = loop,
                        code_brk = Nothing,
                        labels   = [odcl lbl] ++ lbls1 ++ (labels p') ++ lbls2
                     }
    where
        p'  = aux (dn_spc g) p
        brk = code_brk p'

        lbls1 = if isNothing brk then [] else
                    [ olbl (fromJust brk) $ (code_aft p') ++ loop ]
        lbls2 = [olbl lbl bef]

        bef  = code_bef p' ++ if isNothing brk then loop else ""
        loop = ocmd g $ "return " ++ lbl ++ "(_ceu_trl)"
        lbl  = label s "Loop"

-------------------------------------------------------------------------------

aux g s@(Par _ p1 p2) = uni { code_bef=src }
    where
        uni  = up_union_sum p1' p2'
        src  = oln s ++ oblk g (src0 ++ src1 ++ srcM ++ src2)
        src0 = (ocmd g' $ "_ceu_mem->_trails[" ++ show trl ++ "].evt.id = CEU_INPUT__STACKED") ++
               (ocmd g' $ "_ceu_mem->_trails[" ++ show trl ++ "].lbl    = " ++ lbl) ++
               (ocmd g' $ "_ceu_mem->_trails[" ++ show trl ++ "].level  = _ceu_level")
        src1 = oblk g' (code_bef p1')
        srcM = spc g ++ "/* with */\n" ++ (ocmd dnz $ "case " ++ lbl ++ ":")
        src2 = oblk g' (code_bef p2')
        g'   = dn_spc g
        p1'  = aux (dn_spc g') p1
        p2'  = aux (dn_spc g'{trail_0=trl}) p2
        trl  = (trail_0 g) + (trails_n p1')
        lbl  = label s "Par"

aux g s@(Trap _ p) = p' { code_bef=src }
    where
        p'  = aux g' p
        src = oln s ++ (ocmd dnz $ oblk g (code_bef p') ++ "case " ++ lbl ++ ":") ++ clr
        g'  = dn_spc g{ traps = s:(traps g) }
        lbl = label s "Trap"
        clr = oblk g $ spc g' ++ "// clear\n" ++
              (ocmd g' $ "memset(&_ceu_mem->_trails[" ++ t0 ++ "], 0, " ++ n ++ ")")
        t0  = show $ trail_0 g
        n   = (show $ trails_n p') ++ "*sizeof(tceu_trl)"

aux g s@(Escape _ k) = upz { code_bef=src }
    where
        src = oln s ++ (ocmd g $ "CEU_GOTO(" ++ (label ((traps g)!!k) "Trap") ++ ")")
