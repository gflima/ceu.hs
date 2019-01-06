module Ceu.Code.Gen where

import Debug.Trace
import Data.List        (intercalate)
import qualified Data.Set as Set
import Data.Maybe
import Ceu.Grammar.Globals
import Ceu.Grammar.Ann  (Ann(..), toTrails0, toTrailsN, getAnn)
import Ceu.Grammar.Type (Type(..)) --, reducesToType0)
import Ceu.Grammar.Exp  (Exp(..), RawAt(..))
import Ceu.Grammar.Stmt (Stmt(..))
import qualified Ceu.Code.N as N

-------------------------------------------------------------------------------

data Down = Down { traps   :: [Stmt]
                 , vars_dn :: [(ID_Var,Stmt)]
                 , evts_dn :: [(ID_Evt,Stmt)]
                 } -- deriving (Show)

dnz :: Down
dnz = Down { traps   = []
           , vars_dn = []
           , evts_dn = []
           }

-------------------------------------------------------------------------------

data Up = Up { inps     :: [String]
             , tps_up   :: [Type]
             , vars_up  :: [(String,Type)]
             , evts_up  :: [String]
             , code_dcl :: String
             , code_bef :: String
             , code_mid :: String
             , code_brk :: Maybe String
             , code_aft :: String
             }
    deriving Show

upz :: Up
upz = Up { inps     = []
         , tps_up   = []
         , vars_up  = []
         , evts_up  = []
         , code_dcl = ""
         , code_bef = ""
         , code_mid = ""
         , code_brk = Nothing
         , code_aft = ""
         }

up_union :: Up -> Up -> Up
up_union u1 u2 = upz { inps     = (inps     u1) ++ (inps     u2)
                     , tps_up   = (tps_up   u1) ++ (tps_up   u2)
                     , vars_up  = (vars_up  u1) ++ (vars_up  u2)
                     , evts_up  = (evts_up  u1) ++ (evts_up  u2)
                     , code_dcl = (code_dcl u1) ++ (code_dcl u2)
                     , code_bef = ""
                     , code_mid = (code_mid u1) ++ (code_mid u2)
                     , code_brk = Nothing
                     , code_aft = ""
                     }

-------------------------------------------------------------------------------

ocmd :: String -> String
ocmd str = str ++ ";\n"

oblk :: String -> String
oblk str = "{\n" ++ str ++ "}\n"

oln :: Ann -> String
oln z = "//#line " ++ (show ln) ++ " \"" ++ file ++ "\" " ++ comm ++ "\n"
    where
        (file,ln,_) = source z
        comm        = "// " ++ (name z)

odcl :: String -> String
odcl lbl = "static void " ++ lbl ++ " (tceu_stk* _ceu_stk);\n\n"

olbl :: String -> String -> String
olbl lbl src = "static void " ++ lbl ++ " (tceu_stk* _ceu_stk) " ++
                 oblk src ++ "\n"

ofunc :: Stmt -> String -> String
ofunc (FuncI _ func (TypeF inp out) (Just imp) _) src =
    "static " ++ tp2use out ++ " CEU_FUNC_" ++ func ++ "__" ++ inp' ++ " (" ++ inp' ++ " _ceu_arg) "
              ++ oblk src ++ "\n"
    where
        inp' = tp2use inp

-------------------------------------------------------------------------------

getEnv :: [(String,Stmt)] -> String -> Stmt
getEnv ((v1,s):l) v2 | v1==v2    = s
                     | otherwise = getEnv l v2
getEnv _          v2 = error v2

getEnvVar env var = if var == "_INPUT" then "_CEU_INPUT" else
                            "CEU_VAR_" ++ var ++ "__" ++ (show $ nn $ getAnn $ getEnv env var)

getEnvEvt env evt = "CEU_EVENT_" ++ evt ++ "__" ++ (show $ nn $ getAnn $ getEnv env evt)

-------------------------------------------------------------------------------

expr :: [(ID_Var,Stmt)] -> Exp -> ([Type],String)
expr vars (RawE  _ raws)   = fold_raws vars raws
expr _    (Const _ n)      = ([], show n)
expr vars (Read  _ id)     = ([], getEnvVar vars id)
expr _    (Unit  _)        = ([], "CEU_UNIT")
--expr vars e@(Tuple _ exps) = "({ tceu__int__int __ceu_" ++ n ++ " = {" ++ vs ++ "}; __ceu_" ++ n ++ ";})"
expr vars e@(Tuple z exps) = ([type_ z]++tps', "((" ++ (tp2use $ type_ z) ++ "){" ++ srcs' ++ "})")
    where
        exps' :: [([Type],String)]
        exps' = map (expr vars) exps

        tps' :: [Type]
        tps' = concat $ map fst exps'

        srcs' :: String
        srcs'= intercalate "," $ map snd exps'

expr vars (Call _ func e) = (tps, "(CEU_FUNC_" ++ id' func ++ "__" ++ (tp2use tp)
                                            ++ "(" ++ op ++ src ++ "))")
                                  where
                                    (tps,src) = expr vars e
                                    id' "(+)"  = "Add"  -- TODO_02: names
                                    id' "(-)"  = "Sub"
                                    id' "(*)"  = "Mul"
                                    id' "(/)"  = "Div"
                                    id' "(==)" = "Eq"
                                    id' "(<=)" = "Lte"
                                    id' x      = x

                                    tp = type_ $ getAnn e
                                    op = case tp of
                                            Type1 _   -> ""
                                            otherwise -> "&"

fold_raws :: [(ID_Var,Stmt)] -> [RawAt] -> ([Type],String)
fold_raws vars raws = (tps, take ((length src)-2) (drop 1 src)) where
    (tps,src) = aux vars raws
    aux _    [] = ([], "")
    aux vars ((RawAtE e):l) = cat (expr vars e) (aux vars l)
    aux vars ((RawAtS s):l) = cat ([],s)        (aux vars l)

    cat (l1,l2) (l1',l2') = (l1++l1',l2++l2')

-------------------------------------------------------------------------------

label :: Ann -> String -> String
label z lbl = "CEU_CODE_" ++ (show $ nn z) ++ "_" ++ lbl

stmt :: Stmt -> [(String,Int)] -> [(String,String)]
stmt p h = [
      ("CEU_TCEU_NTRL", n2tp $ toTrailsN (getAnn p'))
    , ("CEU_TRAILS_N",  show $ toTrailsN (getAnn p'))
    -- TODO: unify all dcls/types outputs
    , ("CEU_INPS",      concat $ map (\inp->s++"CEU_INPUT_"++inp++",\n") $ inps    up)
    , ("CEU_EVTS",      concat $ map (\evt->s++"CEU_EVENT_"++evt++",\n") $ evts_up up)
    , ("CEU_TYPES",     concat $ rmdups $ map (\tp->tp2dcl tp++"\n")
                                        -- $ filter (not.reducesToType0)
                                        $ tps_up up)
    , ("CEU_VARS",      concat $ map (\(var,tp)->s++tp2use tp++" "++var++";\n")
                               -- $ filter (not.reducesToType0.snd)
                               $ vars_up up)
    , ("CEU_HISTORY",   concat $ map (\(evt,v) ->s++"_CEU_INPUT="++show v++"; ceu_input(CEU_INPUT_"++evt++")"++";\n" ) h)
    , ("CEU_CODE",      code_dcl up ++ root2 ++ code_mid up ++ root1 )
    ]
    where
        p'    = N.add p
        --p'    = traceShowId $ N.add p
        up    = aux dnz p'
        root1 = olbl "CEU_CODE_ROOT" (code_bef up)
        root2 = case code_brk up of
                    Nothing  -> ""
                    Just lbl -> olbl lbl (code_aft up)

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
tp2use Type0         = "tceu_unit"
tp2use (Type1 "Int") = "int"
tp2use (TypeN tps)   = "tceu__" ++ intercalate "__" (map (\tp -> tp2use tp) tps)
tp2use tp            = error $ show tp

tp2dcl :: Type -> String
tp2dcl tp@(TypeN tps) =
    "typedef struct " ++ use ++ " {\n"  ++
    (snd $ foldr (\tp (n,s) -> (n-1, "    " ++ tp2use tp ++ " _" ++ show n ++ ";\n" ++ s))
                 (length tps,"")
                 tps)   ++
                 --(filter (not.isType0) tps))   ++
    "} " ++ use ++ ";\n"
    where
        use = tp2use tp
        --isType0 Type0 = True
        --isType0 _     = False
tp2dcl _ = ""


-------------------------------------------------------------------------------

aux :: Down -> Stmt -> Up

aux dn (Nop   z)      = upz { code_bef=(oln z) }
aux dn (Halt  z)      = upz { code_bef=(oln z) }
aux dn (RawS  z raws) = upz { code_bef=(oln z)++src++";\n", tps_up=tps }
                            where (tps,src) = fold_raws (vars_dn dn) raws
aux dn (Inp   _ id p) = p' { inps=id:(inps p') } where p'=(aux dn p)
aux dn (Out   _ id p) = aux dn p

-------------------------------------------------------------------------------

aux dn s@(Evt z id p) = p' { evts_up=(id++"__"++(show$nn z)):(evts_up p') }
    where
        p'  = aux dn' p
        dn' = dn{ evts_dn = (id,s):(evts_dn dn) }

aux dn s@(Var z id tp p) = p' {
                                code_dcl = dcl' ++ (code_dcl p'),
                                code_bef = bef' ++ (code_bef p'),
                                tps_up   = tp:(tps_up p'),
                                vars_up  = var ++ (vars_up p')
                           }
    where
        p'  = aux dn' p
        dn' = dn{ vars_dn = (id,s):(vars_dn dn) }
        brk = code_brk p'

        (var,dcl',bef') = f (if id=="_ret" then (Just "") else brk) where
            f Nothing  = ([],
                          "#define CEU_VAR_" ++ id' ++ " " ++ id' ++ "\n",
                          ocmd $ tp2use tp ++ " " ++ id')
            f (Just _) = ([(id',tp)],
                          "#define CEU_VAR_" ++ id' ++ " " ++ "CEU_APP.root."++id' ++ "\n",
                          "")
            id'  = id ++ "__" ++ (show $ nn z)

aux dn s@(Func z id (TypeF inp out) p) = p'
    where
        p'  = aux dn' p
        dn' = dn { vars_dn = (id',s):(vars_dn dn) }
        id' = id ++ "__" ++ (show $ nn z)

aux dn (FuncI z id (TypeF inp out) Nothing p) = p' { tps_up=inp:out:(tps_up p') }
    where p' = aux dn p

aux dn s@(FuncI z id tp@(TypeF inp out) (Just imp) p) =
    uni {
        code_bef = code_bef p',
        code_mid = (code_mid uni) ++ func,
        code_brk = code_brk p',
        code_aft = code_aft p'
    }
    where
        uni  = up_union imp' p'
        p'   = aux dn p
        imp' = aux dn imp
        func = ofunc s (vars ++ code_bef imp')
        vars = concat $ map (\(var,tp)->tp2use tp++" "++var++";\n")
                           -- $ filter (not.reducesToType0.snd)
                           $ vars_up imp'

aux dn (Write _ LAny       _)   = upz
aux dn (Write z (LVar var) exp) = upz { code_bef=src', tps_up=tps }
    where
        vars = vars_dn dn
        (tps,src) = expr vars exp
        src' = (oln z ++ (ocmd $ (getEnvVar vars var) ++ " = " ++ src))

aux dn (Write z tup exp) = upz { code_bef=src_write, tps_up=tps_exp }
    where
        (tps_exp,src_exp) = expr (vars_dn dn) exp
        src_write = (oln z ++ (ocmd $ aux' tup src_exp))
        vars = vars_dn dn

        aux' LAny          _   = ""
        aux' (LVar var)    exp = oln z ++ (ocmd $ (getEnvVar vars var) ++ " = " ++ exp)
        aux' (LTuple locs) exp =
            snd $ foldl (\(n,ret) loc -> (n+1, aux' loc (exp++"._"++(show n)) ++ ret))
                                         (1,"")
                                         locs

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

aux dn (EmitExt z ext exp) = upz { code_bef=src, tps_up=etps }
    where
        src = oln z ++ (ocmd $ "ceu_callback_output_" ++ ext ++ "(" ++ esrc ++ ")")
        (etps,esrc) = maybe ([],"") (expr (vars_dn dn)) exp

aux dn (EmitEvt z evt) = upz { code_bef=(oln z)++bef }
    where
        bef = oblk $
              (ocmd $ "tceu_bcast __ceu_cst = {" ++ id' ++ "," ++ show trl0 ++ "," ++ show trlN++"}") ++
              (ocmd $ "tceu_stk   __ceu_stk = { _ceu_stk->level+1, 1, 0, _ceu_stk }") ++
              (ocmd $ "_ceu_stk->trail = " ++ (show $ toTrails0 z)) ++
              (ocmd $ "ceu_bcast(&__ceu_cst, &__ceu_stk)")         ++
              (ocmd $ "if (!_ceu_stk->is_alive) return")

        id' = getEnvEvt (evts_dn dn) evt
        (trl0,trlN) = trails $ getAnn $ getEnv (evts_dn dn) evt

-------------------------------------------------------------------------------

aux dn (Seq z p1 p2) = (up_union p1' p2') {
                            code_bef = oln z ++ bef,
                            --code_bef = bef,
                            code_mid = code_mid p2' ++ mid ++ code_mid p1',
                            code_brk = brk,
                            code_aft = aft
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

        (bef, mid, brk, aft) = f brk1 brk2 where
            f Nothing  Nothing  = (bef1++bef2, "",     Nothing, "")
            f Nothing  (Just _) = (bef1++bef2, "",     brk2,    aft2)
            f (Just _) Nothing  = (bef1,       "",     brk1,    aft1++bef2)
            f (Just x) (Just _) = (bef1,       fmid x, brk2,    aft2)
                where
                    fmid x = olbl x (aft1++bef2)

-------------------------------------------------------------------------------

aux dn (If z exp p1 p2) = (up_union p1' p2') {
                                code_bef = bef,
                                code_mid = mid1++mid2 ++ code_mid p2' ++ code_mid p1',
                                code_brk = brk,
                                code_aft = "",
                                tps_up   = etps
                            }
    where
        p1' = aux dn p1
        p2' = aux dn p2
        (etps,esrc) = expr (vars_dn dn) exp

        bef1 = code_bef p1'
        bef2 = code_bef p2'
        brk1 = code_brk p1'
        brk2 = code_brk p2'
        aft1 = code_aft p1'
        aft2 = code_aft p2'

        bef = oln z ++ "if (" ++ esrc ++ ")\n" ++ oblk bef1'
                    ++ "else\n"                ++ oblk bef2'

        (bef1',bef2',mid1,mid2,brk) = f brk1 brk2 where
            f Nothing  Nothing  = (bef1,       bef2,       "",          "",          Nothing)
            f Nothing  (Just y) = (bef1++join, bef2,       "",          fmid y aft2, Just lbl)
            f (Just x) Nothing  = (bef1,       bef2++join, fmid x aft1, [],          Just lbl)
            f (Just x) (Just y) = (bef1,       bef2,       fmid x aft1, fmid y aft2, Just lbl)

            join = ocmd $ "return " ++ lbl ++ "(_ceu_stk)"
            lbl  = label z "If_Join"
            fmid brk aft = olbl brk (aft ++ join)

-------------------------------------------------------------------------------

aux dn (Loop z p) = p' {
                        code_bef = bef',
                        code_mid = dcl ++ pos ++ (code_mid p') ++ pre,
                        code_brk = brk',
                        code_aft = ""
                     }
    where
        p'  = aux dn p
        bef = code_bef p'
        brk = code_brk p'
        aft = code_aft p'

        (bef',dcl,pre,pos,brk') = f brk where
            f Nothing  = (loop, "", "", "", Nothing)
            f (Just x) = (call, odcl lbl,
                                olbl lbl bef,
                                olbl x (aft ++ call),
                                Just $ label z "Nop")

            loop = oln z ++ "while (1)\n" ++ oblk bef
            call = ocmd $ "return " ++ lbl ++ "(_ceu_stk)"
            lbl  = label z "Loop"

-------------------------------------------------------------------------------

aux dn (Par z p1 p2) = (up_union p1' p2') {
                            code_bef = oln z ++ bef,
                            code_mid = aft1' ++ code_mid p1' ++ mid' ++ aft2' ++ code_mid p2',
                            code_brk = brk',
                            code_aft = ""
                         }
    where
        p1'  = aux dn p1
        p2'  = aux dn p2

        bef1 = code_bef p1'
        bef2 = code_bef p2'
        brk1 = code_brk p1'
        brk2 = code_brk p2'
        aft1 = code_aft p1'
        aft2 = code_aft p2'

        bef = (oblk $
                (ocmd $ "tceu_stk __ceu_stk = { _ceu_stk->level+1, 1, "
                                            ++ (show $ toTrails0 $ getAnn p2)
                                            ++ ", _ceu_stk }") ++
                bef' ++
                (ocmd $ "if (!__ceu_stk.is_alive) return")) ++
              bef2

        (bef',mid',brk',aft1',aft2') = f brk1 brk2 where
            f Nothing  Nothing  = (befA, "",                 Nothing,  "",              "")
            f Nothing  (Just y) = (befA, "",                 Just nop, "",              olbl y aft2)
            f (Just x) Nothing  = (befB, olbl lbl1 bef1, Just nop, olbl x aft1, "")
            f (Just x) (Just y) = (befB, olbl lbl1 bef1, Just nop, olbl x aft1, olbl y aft2)

            tmp = "__ceu_tmp_" ++ (show $ nn z)
            befA = oblk $
                    (ocmd $ "tceu_stk* " ++ tmp ++ " = _ceu_stk;") ++
                    (ocmd $ "_ceu_stk = &__ceu_stk")               ++
                    bef1                                           ++
                    (ocmd $ "_ceu_stk = " ++ tmp)

            lbl1 = label (getAnn p1) "Trail1"
            befB = ocmd $ lbl1 ++ "(&__ceu_stk)"
            nop  = label z "Nop"

-------------------------------------------------------------------------------

aux dn s@(Trap z p) = p' {
                        code_bef = bef',
                        code_mid = dcl' ++ mid' ++ (code_mid p'),
                        code_brk = brk',
                        code_aft = aft'
                      }
    where
        p'  = aux dn' p
        dn' = dn{ traps = s:(traps dn) }

        bef = code_bef p'
        brk = code_brk p'
        aft = code_aft p'

        (bef',brk',dcl',mid',aft') = f brk where
            f Nothing  = (bef++lblA++":;\n", Nothing,   escA,            "",         "")
            f (Just x) = (bef,              Just lblB, escB++odcl lblB, olbl x aft, clr)

            clr = oblk $ "// clear\n" ++
                  (ocmd $ "memset(&CEU_APP.root.trails[" ++ t0 ++ "], 0, " ++ sz ++ ")") ++
                  (ocmd $ "ceu_stack_clear(_ceu_stk, " ++ t0 ++ "," ++ n ++ ")")
            t0  = show $ toTrails0 z
            n   = show $ toTrailsN z
            sz  = n ++ "*sizeof(tceu_trl)"

            escA = "#define CEU_ESCAPE_" ++ (show $ nn z) ++ "() goto " ++ lblA ++ "\n"
            escB = "#define CEU_ESCAPE_" ++ (show $ nn z) ++ "() return " ++ lblB ++ "(_ceu_stk)\n"

            lblA = "CEU_TRAP_" ++ (show $ nn z)
            lblB = label z "Trap"

aux dn (Escape z k) = upz {
                        code_bef = oln z ++ (ocmd $ "CEU_ESCAPE_" ++ (show $ nn $ getAnn $ (traps dn)!!k) ++ "()")
                      }
