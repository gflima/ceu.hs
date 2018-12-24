module Ceu.Code.Gen where

import Debug.Trace
import Data.Maybe
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data Down = Down { traps   :: [Stmt All]
                 , trail_0 :: Int
                 , vars_dn :: [(ID_Var,Int)]
                 , evts_dn :: [(ID_Evt,Int)]
                 } -- deriving (Show)

dnz :: Down
dnz = Down { traps   = []
           , trail_0 = 0
           , vars_dn = []
           , evts_dn = []
           }

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

ocmd :: String -> String
ocmd str = str ++ ";\n"

oblk :: String -> String
oblk str = "{\n" ++ str ++ "}\n"

oln :: Stmt All -> String
oln p = "//#line " ++ (show ln) ++ " \"" ++ file ++ "\" " ++ comm ++ "\n"
    where
        Just (file,ln,_) = toSource p
        comm             = "// " ++ (toWord p)

odcl :: String -> String
odcl lbl = "void " ++ lbl ++ " (tceu_stk* _ceu_stk);\n\n"

olbl :: String -> String -> String
olbl lbl src = "void " ++ lbl ++ " (tceu_stk* _ceu_stk) " ++
                 oblk src ++ "\n"

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
    up    = aux dnz (N.add $ traceShowId p)
    root1 = [ olbl "CEU_LABEL_ROOT" (code_bef up) ]
    root2 = case code_brk up of
                Nothing  -> []
                Just lbl -> [ olbl lbl (code_aft up) ]

-------------------------------------------------------------------------------

aux :: Down -> Stmt All -> Up

aux dn s@(Nop   _)      = upz { code_bef=(oln s) }
aux dn s@(Halt  _)      = upz { code_bef=(oln s), code_brk=Just(label s "Halt") }
aux dn s@(Inp   _ id p) = p' { inps=id:(inps p') } where p'=(aux dn p)
aux dn s@(Out   _ id p) = aux dn p

-------------------------------------------------------------------------------

aux dn s@(Evt _ id p) = p' { evts_up=(id++"__"++(show$toN s)):(evts_up p') }
    where
        p'  = aux dn' p
        dn' = dn{ evts_dn = (id,toN s):(evts_dn dn) }

aux dn s@(Var _ id p) = p' { vars_up=(id++"__"++(show$toN s)):(vars_up p') }
    where
        p'  = aux dn' p
        dn' = dn{ vars_dn = (id,toN s):(vars_dn dn) }

aux dn s@(Write _ var exp) = upz { code_bef=src }
    where
        src  = (oln s ++ (ocmd $ "CEU_APP.root." ++ (getID vars var) ++ " = " ++ (expr vars exp)))
        vars = vars_dn dn

-------------------------------------------------------------------------------

aux dn s@(AwaitInp _ ext) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln s ++
              (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].evt = " ++ evt) ++
              (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].lbl = " ++ lbl)
        trl = show $ trail_0 dn
        evt = "CEU_INPUT_" ++ ext
        lbl = label s ("AwaitInp_" ++ ext)

aux dn s@(AwaitEvt _ evt) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln s ++
             (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].evt = " ++ id') ++
             (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].lbl = " ++ lbl)
        trl = show $ trail_0 dn
        id' = "CEU_EVENT_" ++ (getID (evts_dn dn) evt)
        lbl = label s ("AwaitEvt_" ++ evt)

-------------------------------------------------------------------------------

aux dn s@(EmitExt _ ext exp) = upz { code_bef=src }
    where
        src = oln s ++ (ocmd $ "ceu_callback_output_" ++ ext ++ "(" ++ exp' ++ ")")
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr (vars_dn dn) v

aux dn s@(EmitEvt _ evt) = upz { code_bef=emt, code_brk=(Just lbl) }
    where
        emt = oblk $
              (ocmd $ "tceu_range __ceu_rge = {" ++ id' ++ ",0, CEU_TRAILS_N-1}") ++
-- TODO: emit scope
              (ocmd $ "_ceu_nxt->range    = __ceu_rge") ++
              (ocmd $ "_ceu_nxt->params_n = 0") ++
              (ocmd $ "return 1")
        id' = "CEU_EVENT_" ++ (getID (evts_dn dn) evt)
        lbl = label s ("EmitEvt_" ++ evt)

-------------------------------------------------------------------------------

aux dn s@(Seq _ p1 p2) = (up_union_max p1' p2') {
                        code_bef = oln s ++ bef,
                        --code_bef = bef,
                        code_brk = brk,
                        code_aft = aft,
                        labels   = lbls ++ labels p2' ++ labels p1'
                      }
    where
        p1' = aux dn p1
        p2' = aux dn p2

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

aux dn s@(If _ exp p1 p2) = (up_union_max p1' p2') {
                            code_bef = bef,
                            code_brk = Just lbl,
                            labels   = lbls1++lbls2 ++ labels p2' ++ labels p1'
                           }
    where
        p1' = aux dn p1
        p2' = aux dn p2
        bef = oln s ++
              "if (" ++ expr (vars_dn dn) exp ++ ")\n" ++ oblk bef1 ++
              "else\n" ++ oblk bef2

        brk1 = code_brk p1'
        brk2 = code_brk p2'

        bef1 = (code_bef p1') ++ if isNothing brk1 then join else ""
        bef2 = (code_bef p2') ++ if isNothing brk2 then join else ""

        join = ocmd $ "return " ++ lbl ++ "(_ceu_stk)"
        lbl  = label s "If_Join"

        lbls1 = if isNothing brk1 then [] else
                    [ olbl (fromJust brk1) $ (code_aft p1') ++ join ]
        lbls2 = if isNothing brk2 then [] else
                    [ olbl (fromJust brk2) $ (code_aft p2') ++ join ]

-------------------------------------------------------------------------------

aux dn s@(Loop _ p) = (up_copy p') {
                        code_bef = loop,
                        code_brk = Nothing,
                        labels   = [odcl lbl] ++ lbls1 ++ (labels p') ++ lbls2
                     }
    where
        p'  = aux dn p
        brk = code_brk p'

        lbls1 = if isNothing brk then [] else
                    [ olbl (fromJust brk) $ (code_aft p') ++ loop ]
        lbls2 = [olbl lbl bef]

        bef  = code_bef p' ++ if isNothing brk then loop else ""
        loop = ocmd $ "return " ++ lbl ++ "(_ceu_stk)"
        lbl  = label s "Loop"

-------------------------------------------------------------------------------

aux dn s@(Par _ p1 p2) = (up_union_sum p1' p2') {
                            code_bef = oln s ++ bef,
                            labels   = lbl11 ++ labels p1' ++ lbl10 ++ lbls2 ++ labels p2'
                         }
    where
        p1'  = aux dn p1
        p2'  = aux dn{trail_0=trl} p2
        trl  = (trail_0 dn) + (trails_n p1')

        brk1 = code_brk p1'
        brk2 = code_brk p2'

        bef = (oblk $
                (ocmd $ "tceu_stk __ceu_stk_new = { {}, 1, 0, _ceu_stk }")  ++
                (ocmd $ "_ceu_stk->trl = " ++ (show trl))                   ++
                (ocmd $ bef1 ++ "(&__ceu_stk_new)")                         ++
                (ocmd $ "if (!_ceu_stk->is_alive) return"))                 ++
              (code_bef p2')

        lbl10 = [ olbl bef1 (code_bef p1') ]
        lbl11 = if isNothing brk1 then [] else [ olbl (fromJust brk1) (code_aft p1') ]
        lbls2 = if isNothing brk2 then [] else [ olbl (fromJust brk2) (code_aft p2') ]
        bef1  = label p1 "Trail1"

-------------------------------------------------------------------------------

aux dn s@(Trap _ p) = (up_copy p') {
                        code_bef = code_bef p',
                        code_brk = Just lbl,
                        code_aft = clr,
                        labels   = [odcl lbl] ++ (labels p') ++ aft
                     }
    where
        p'  = aux dn' p
        dn' = dn{ traps = s:(traps dn) }
        lbl = label s "Trap"

        aft = if isNothing brk then [] else
                [ olbl (fromJust brk) (code_aft p') ]
        brk = code_brk p'

        clr = oblk $ "// clear\n" ++
              (ocmd $ "memset(&CEU_APP.root.trails[" ++ t0 ++ "], 0, " ++ sz ++ ")") ++
              (ocmd $ "ceu_stack_clear(_ceu_stk, " ++ t0 ++ "," ++ n ++ ")")
        t0  = show $ trail_0 dn
        n   = show $ trails_n p'
        sz  = n ++ "*sizeof(tceu_trl)"

aux dn s@(Escape _ k) = upz { code_bef=src, code_brk=Just(label s "Escape") }
    where
        src = oln s ++ (ocmd $ "return " ++ (label ((traps dn)!!k) "Trap") ++ "(_ceu_stk)")
