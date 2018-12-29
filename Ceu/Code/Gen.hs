module Ceu.Code.Gen where

import Debug.Trace
import Data.List        (intercalate)
import qualified Data.Set as Set
import Data.Maybe
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann  (Ann(..))
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Type (Type(..))
import Ceu.Grammar.Exp  (Exp(..), RawAt(..))
import Ceu.Grammar.Stmt (Stmt(..), getAnn)
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data Down = Down { traps   :: [Stmt All]
                 , vars_dn :: [(ID_Var,Stmt All)]
                 , evts_dn :: [(ID_Evt,Stmt All)]
                 } -- deriving (Show)

dnz :: Down
dnz = Down { traps   = []
           , vars_dn = []
           , evts_dn = []
           }

-------------------------------------------------------------------------------

data Up = Up { inps     :: [String]
             , tps_up   :: [Type]
             , vars_up  :: [(String,String)]
             , evts_up  :: [String]
             , code_bef :: String
             , code_brk :: Maybe String
             , code_aft :: String
             , labels   :: [String]
             }
    deriving Show

upz :: Up
upz = Up { inps     = []
         , tps_up   = []
         , vars_up  = []
         , evts_up  = []
         , code_bef = ""
         , code_brk = Nothing
         , code_aft = ""
         , labels   = []
         }

up_union :: Up -> Up -> Up
up_union u1 u2 = upz { inps     = (inps    u1) ++ (inps    u2)
                     , tps_up   = (tps_up  u1) ++ (tps_up  u2)
                     , vars_up  = (vars_up u1) ++ (vars_up u2)
                     , evts_up  = (evts_up u1) ++ (evts_up u2)
                     , code_bef = ""
                     , code_brk = Nothing
                     , code_aft = ""
                     , labels   = []
                     }

-------------------------------------------------------------------------------

ocmd :: String -> String
ocmd str = str ++ ";\n"

oblk :: String -> String
oblk str = "{\n" ++ str ++ "}\n"

oln :: Ann a => a -> String
oln ann = "//#line " ++ (show ln) ++ " \"" ++ file ++ "\" " ++ comm ++ "\n"
    where
        (file,ln,_) = getSource ann
        comm        = "// " ++ (getName ann)

odcl :: String -> String
odcl lbl = "static void " ++ lbl ++ " (tceu_stk* _ceu_stk);\n\n"

olbl :: String -> String -> String
olbl lbl src = "static void " ++ lbl ++ " (tceu_stk* _ceu_stk) " ++
                 oblk src ++ "\n"

-------------------------------------------------------------------------------

getEnv :: [(String,Stmt All)] -> String -> Stmt All
getEnv ((v1,s):l) v2 | v1==v2    = s
                     | otherwise = getEnv l v2

getEnvVar env var = if var == "_INPUT" then "_CEU_INPUT" else "CEU_APP.root."++id'
                    where
                        id' = var ++ "__" ++ (show $ getN $ getAnn $ getEnv env var)

getEnvEvt env evt = "CEU_EVENT_" ++ evt ++ "__" ++ (show $ getN $ getAnn $ getEnv env evt)

-------------------------------------------------------------------------------

expr :: [(ID_Var,Stmt All)] -> Exp All -> String
expr vars (RawE  _ raw)    = fold_raw vars raw
expr vars (Const _ n)      = show n
expr vars (Read  _ id)     = getEnvVar vars id
--expr vars e@(Tuple _ exps) = "({ tceu__int__int __ceu_" ++ n ++ " = {" ++ vs ++ "}; __ceu_" ++ n ++ ";})"
expr vars e@(Tuple z exps) = "{" ++ vs ++ "}"
    where
        n  = show $ getN z
        vs = intercalate "," (map (\e -> expr vars e) (filter (not.isUnit) exps))
        isUnit (Unit _) = True
        isUnit _        = False

expr vars (Call  _ "negate" e) = "(negate(" ++ (expr vars e) ++ "))"
expr vars (Call  _ "(+)"    e) = "(plus(&" ++ e' ++ "))"
                                    where e' = expr vars e
expr vars (Call  _ "(-)"    e) = "(minus(&" ++ e' ++ "))"
                                    where e' = expr vars e
expr vars (Call  _ "(*)"    e) = "(times(&" ++ e' ++ "))"
                                    where e' = expr vars e
expr vars (Call  _ "(/)"    e) = "(div(&" ++ e' ++ "))"
                                    where e' = expr vars e
expr vars (Call  _ "(==)"   e) = "(equal(&" ++ e' ++ "))"
                                    where e' = expr vars e
expr vars (Call  _ "(<=)"   e) = "(lte(&" ++ e' ++ "))"
                                    where e' = expr vars e

expr _ e = error (show e)

fold_raw :: [(ID_Var,Stmt All)] -> [RawAt All] -> String
fold_raw vars raw = take ((length raw')-2) (drop 1 raw') where
    raw' = aux vars raw
    aux vars [] = ""
    aux vars ((RawAtE e):l) = (expr vars e) ++ (aux vars l)
    aux vars ((RawAtS s):l) = s ++ (aux vars l)

-------------------------------------------------------------------------------

label :: Ann a => a -> String -> String
label ann lbl = "CEU_LABEL_" ++ (show $ getN ann) ++ "_" ++ lbl

stmt :: Stmt Source -> [(String,Int)] -> [(String,String)]
stmt p h = [
      ("CEU_TCEU_NTRL", n2tp $ toTrailsN (getAnn p'))
    , ("CEU_TRAILS_N",  show $ toTrailsN (getAnn p'))
    -- TODO: unify all dcls/types outputs
    , ("CEU_INPS",      concat $ map (\inp->s++"CEU_INPUT_"++inp++",\n") $ inps    up)
    , ("CEU_EVTS",      concat $ map (\evt->s++"CEU_EVENT_"++evt++",\n") $ evts_up up)
    , ("CEU_TYPES",     concat $ rmdups $ map (\tp->tp2dcl tp++"\n") $ tps_up up)
    , ("CEU_VARS",      concat $ map (\(var,tp)->s++tp++" "++var++";\n") $ filter (\(_,tp)->tp/="void") $ vars_up up)
    , ("CEU_HISTORY",   concat $ map (\(evt,v) ->s++"_CEU_INPUT="++show v++"; ceu_input(CEU_INPUT_"++evt++")"++";\n" ) h)
    , ("CEU_LABELS",    concat $ root2 ++ labels up ++ root1 )
    ]
    where
        p'    = N.add p
        --p'    = traceShowId $ N.add p
        up    = aux dnz p'
        root1 = [ olbl "CEU_LABEL_ROOT" (code_bef up) ]
        root2 = case code_brk up of
                    Nothing  -> []
                    Just lbl -> [ olbl lbl (code_aft up) ]

        s = "    "

        n2tp :: Int -> String
        n2tp v = if v>2^32 then "u64" else if v>2^16 then "u32" else if v>2^8 then "u16" else "u8"

        rmdups :: Ord a => [a] -> [a]
        rmdups = rmdups' Set.empty where
          rmdups' _ [] = []
          rmdups' a (b : c) = if Set.member b a
            then rmdups' a c
            else b : rmdups' (Set.insert b a) c

-------------------------------------------------------------------------------

tp2use :: Type -> String
tp2use Type0         = "void"
tp2use (Type1 "Int") = "int"
tp2use (TypeN tps)   = "tceu__" ++ intercalate "__" (map (\tp -> tp2use tp) tps)

tp2dcl :: Type -> String
tp2dcl tp@(TypeN tps) =
    "typedef struct " ++ use ++ " {\n"  ++
    (snd $ foldr (\tp (n,s) -> (n-1, "    " ++ tp2use tp ++ " _" ++ show n ++ ";\n" ++ s))
                 (length tps,"")
                 (filter (not.isType0) tps))   ++
    "} " ++ use ++ ";\n"
    where
        use = tp2use tp
        isType0 Type0 = True
        isType0 _     = False
tp2dcl _ = ""


-------------------------------------------------------------------------------

aux :: Down -> Stmt All -> Up

aux dn (Nop   z)      = upz { code_bef=(oln z) }
aux dn (Halt  z)      = upz { code_bef=(oln z), code_brk=Just(label z "Halt") }
aux dn (RawS  z raw)  = upz { code_bef=(oln z)++(fold_raw (vars_dn dn) raw)++";\n" }
aux dn (Inp   _ id p) = p' { inps=id:(inps p') } where p'=(aux dn p)
aux dn (Out   _ id p) = aux dn p

-------------------------------------------------------------------------------

aux dn s@(Evt z id p) = p' { evts_up=(id++"__"++(show$getN z)):(evts_up p') }
    where
        p'  = aux dn' p
        dn' = dn{ evts_dn = (id,s):(evts_dn dn) }

aux dn s@(Var z id tp p) = p' { tps_up=tp:(tps_up p'), vars_up=(id',tp'):(vars_up p') }
    where
        p'  = aux dn' p
        dn' = dn{ vars_dn = (id,s):(vars_dn dn) }
        id' = id ++ "__" ++ (show $ getN z)
        tp' = tp2use tp

aux dn s@(Func z id (TypeF inp out) p) = p' { tps_up=inp:out:(tps_up p') }
    where
        p'  = aux dn' p
        dn' = dn --{ vars_dn = (id,s):(vars_dn dn) }
        --id' = id ++ "__" ++ (show $ getN z)

aux dn (Write z var exp) = upz { code_bef=src }
    where
        src  = case tp of
                Type0     -> ""
                otherwise -> (oln z ++ (ocmd $ (getEnvVar vars var) ++ " = " ++ (expr vars exp)))
        vars = vars_dn dn
        (Var _ _ tp _) = getEnv vars var

-------------------------------------------------------------------------------

aux dn (AwaitInp z ext) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln z ++
              (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].evt = " ++ evt) ++
              (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].lbl = " ++ lbl)
        trl = show $ toTrails0 z
        evt = "CEU_INPUT_" ++ ext
        lbl = label z ("AwaitInp_" ++ ext)

aux dn (AwaitEvt z evt) = upz { code_bef=src, code_brk=(Just lbl) }
    where
        src = oln z ++
             (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].evt = " ++ id') ++
             (ocmd $ "CEU_APP.root.trails[" ++ trl ++ "].lbl = " ++ lbl)
        trl = show $ toTrails0 z
        id' = getEnvEvt (evts_dn dn) evt
        lbl = label z ("AwaitEvt_" ++ evt)

-------------------------------------------------------------------------------

aux dn (EmitExt z ext exp) = upz { code_bef=src }
    where
        src = oln z ++ (ocmd $ "ceu_callback_output_" ++ ext ++ "(" ++ exp' ++ ")")
        exp' = case exp of
            Nothing  -> ""
            (Just v) -> expr (vars_dn dn) v

aux dn (EmitEvt z evt) = upz { code_bef=(oln z)++bef }
    where
        bef = oblk $
              (ocmd $ "tceu_bcast __ceu_cst = {" ++ id' ++ "," ++ show trl0 ++ "," ++ show trlN++"}") ++
              (ocmd $ "tceu_stk   __ceu_stk = { _ceu_stk->level+1, 1, 0, _ceu_stk }") ++
              (ocmd $ "_ceu_stk->trail = " ++ (show $ toTrails0 z)) ++
              (ocmd $ "ceu_bcast(&__ceu_cst, &__ceu_stk)")         ++
              (ocmd $ "if (!_ceu_stk->is_alive) return")

        id' = getEnvEvt (evts_dn dn) evt
        (trl0,trlN) = getTrails $ getAnn $ getEnv (evts_dn dn) evt

-------------------------------------------------------------------------------

aux dn (Seq z p1 p2) = (up_union p1' p2') {
                            code_bef = oln z ++ bef,
                            --code_bef = bef,
                            code_brk = brk,
                            code_aft = aft,
                            labels   = labels p2' ++ lbls ++ labels p1'
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

aux dn (If z exp p1 p2) = (up_union p1' p2') {
                                code_bef = bef,
                                code_brk = Just lbl,
                                labels   = lbls1++lbls2 ++ labels p2' ++ labels p1'
                            }
    where
        p1' = aux dn p1
        p2' = aux dn p2
        bef = oln z ++
              "if (" ++ expr (vars_dn dn) exp ++ ")\n" ++ oblk bef1 ++
              "else\n" ++ oblk bef2

        brk1 = code_brk p1'
        brk2 = code_brk p2'

        bef1 = (code_bef p1') ++ if isNothing brk1 then join else ""
        bef2 = (code_bef p2') ++ if isNothing brk2 then join else ""

        join = ocmd $ "return " ++ lbl ++ "(_ceu_stk)"
        lbl  = label z "If_Join"

        lbls1 = if isNothing brk1 then [] else
                    [ olbl (fromJust brk1) $ (code_aft p1') ++ join ]
        lbls2 = if isNothing brk2 then [] else
                    [ olbl (fromJust brk2) $ (code_aft p2') ++ join ]

-------------------------------------------------------------------------------

aux dn (Loop z p) = p' {
                        code_bef = loop,
                        code_brk = Nothing,
                        code_aft = "",
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
        lbl  = label z "Loop"

-------------------------------------------------------------------------------

aux dn (Par z p1 p2) = (up_union p1' p2') {
                            code_bef = oln z ++ bef,
                            labels   = lbl11 ++ labels p1' ++ lbl10 ++ lbls2 ++ labels p2'
                         }
    where
        p1'  = aux dn p1
        p2'  = aux dn p2

        brk1 = code_brk p1'
        brk2 = code_brk p2'

        bef = (oblk $
                (ocmd $ "tceu_stk __ceu_stk = { _ceu_stk->level+1, 1, 0, _ceu_stk }") ++
                (ocmd $ "_ceu_stk->trail = " ++ (show $ toTrails0 $ getAnn p2)) ++
                (ocmd $ bef1 ++ "(&__ceu_stk)")             ++
                (ocmd $ "if (!_ceu_stk->is_alive) return")) ++
              (code_bef p2')

        lbl10 = [ olbl bef1 (code_bef p1') ]
        lbl11 = if isNothing brk1 then [] else [ olbl (fromJust brk1) (code_aft p1') ]
        lbls2 = if isNothing brk2 then [] else [ olbl (fromJust brk2) (code_aft p2') ]
        bef1  = label (getAnn p1) "Trail1"

-------------------------------------------------------------------------------

aux dn s@(Trap z p) = p' {
                        code_bef = code_bef p',
                        code_brk = Just lbl,
                        code_aft = clr,
                        labels   = [odcl lbl] ++ (labels p') ++ aft
                      }
    where
        p'  = aux dn' p
        dn' = dn{ traps = s:(traps dn) }
        lbl = label z "Trap"

        aft = if isNothing brk then [] else
                [ olbl (fromJust brk) (code_aft p') ]
        brk = code_brk p'

        clr = oblk $ "// clear\n" ++
              (ocmd $ "memset(&CEU_APP.root.trails[" ++ t0 ++ "], 0, " ++ sz ++ ")") ++
              (ocmd $ "ceu_stack_clear(_ceu_stk, " ++ t0 ++ "," ++ n ++ ")")
        t0  = show $ toTrails0 z
        n   = show $ toTrailsN z
        sz  = n ++ "*sizeof(tceu_trl)"

aux dn (Escape z k) = upz { code_bef=src, code_brk=Just(label z "Escape") }
    where
        src = oln z ++ (ocmd $ "return " ++ (label (getAnn $ (traps dn)!!k) "Trap") ++ "(_ceu_stk)")
