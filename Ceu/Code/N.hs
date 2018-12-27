module Ceu.Code.N where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..), RawAt(..))
import Ceu.Grammar.Stmt (Stmt(..))

add :: (Stmt Source) -> (Stmt All)
add p = p' where (_,_,p') = stmt 0 0 p

stmt :: Int -> Int -> (Stmt Source) -> (Int, Int, Stmt All)

stmt n trl0 (Nop src) = (n+1,1, Nop All{source=src,n=n,trails=(trl0,1)})

stmt n trl0 (Var src id tp p) =
    (n',ts', Var All{source=src,n=n,trails=(trl0,ts')} id tp p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Inp src id p) =
    (n',ts', Inp All{source=src,n=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Out src id p) =
    (n',ts', Out All{source=src,n=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Evt src id p) =
    (n',ts', Evt All{source=src,n=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (CodI src id inp out p) =
    (n',ts', CodI All{source=src,n=n,trails=(trl0,ts')} id inp out p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Write src var exp) =
    (n',1, Write All{source=src,n=n,trails=(trl0,1)} var exp')
    where
        (n',exp') = expr (n+1) exp

stmt n trl0 (AwaitInp src ext) =
    (n+1,1, AwaitInp All{source=src,n=n,trails=(trl0,1)} ext)

stmt n trl0 (EmitExt src ext Nothing) =
    (n+1,1, EmitExt All{source=src,n=n,trails=(trl0,1)} ext Nothing)
stmt n trl0 (EmitExt src ext (Just exp)) =
    (n',1, EmitExt All{source=src,n=n,trails=(trl0,1)} ext (Just exp'))
    where
        (n',exp') = expr (n+1) exp

stmt n trl0 (AwaitEvt src evt) =
    (n+1,1, AwaitEvt All{source=src,n=n,trails=(trl0,1)} evt)

stmt n trl0 (EmitEvt src evt) =
    (n+1,1, EmitEvt All{source=src,n=n,trails=(trl0,1)} evt)

stmt n trl0 (If src exp p1 p2) =
    (n2',mx, If All{source=src,n=n,trails=(trl0,mx)} exp' p1' p2')
    where
        (n',exp')      = expr (n+1) exp
        (n1',ts1',p1') = stmt n'    trl0 p1
        (n2',ts2',p2') = stmt n1'   trl0 p2
        mx = max ts1' ts2'

stmt n trl0 (Seq src p1 p2) =
    (n2',mx, Seq All{source=src,n=n,trails=(trl0,mx)} p1' p2')
    where
        (n1',ts2',p1') = stmt (n+1) trl0 p1
        (n2',ts1',p2') = stmt n1'   trl0 p2
        mx = max ts1' ts2'

stmt n trl0 (Loop src p) =
    (n',ts', Loop All{source=src,n=n,trails=(trl0,ts')} p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Par src p1 p2) =
    (n2',sm, Par All{source=src,n=n,trails=(trl0,sm)} p1' p2')
    where
        (n1',ts1',p1') = stmt (n+1) trl0        p1
        (n2',ts2',p2') = stmt n1'   (trl0+ts1') p2
        sm = ts1' + ts2'

stmt n trl0 (Trap src p) =
    (n',ts', Trap All{source=src,n=n,trails=(trl0,ts')} p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Escape src k) = (n+1, 1, Escape All{source=src,n=n,trails=(trl0,1)} k)
stmt n trl0 (Halt src)     = (n+1, 1, Halt   All{source=src,n=n,trails=(trl0,1)})
stmt n trl0 (RawS src raw) = (n',  1, RawS   All{source=src,n=n,trails=(trl0,1)} raw')
    where
        (n',raw') = fold_raw n raw

stmt n trl0 p = error (show p)

-------------------------------------------------------------------------------

expr :: Int -> (Exp Source) -> (Int, Exp All)
expr n (RawE  src raw) = (n', RawE All{source=src,n=n,trails=(0,0)} raw') where
                            (n',raw') = fold_raw n raw
expr n (Const src v)   = (n+1, Const All{source=src,n=n,trails=(0,0)} v)
expr n (Read  src id)  = (n+1, Read  All{source=src,n=n,trails=(0,0)} id)

expr n (Call src1 id (Tuple src2 [e1,e2])) =
    (n2', Call All{source=src1,n=n,trails=(0,0)} id
            (Tuple All{source=src2,n=n+1,trails=(0,0)} [e1',e2']))
    where
        (n1',e1') = expr (n+2) e1
        (n2',e2') = expr n1'   e2
expr n (Call src id e) = (n', Call All{source=src,n=n,trails=(0,0)} id e')
    where
        (n',e') = expr (n+1) e

fold_raw :: Int -> [RawAt Source] -> (Int, [RawAt All])
fold_raw n raw =
    foldr (\r (n,l) -> case r of
                        (RawAtE e) -> (n',(RawAtE e'):l) where (n',e') = expr n e
                        (RawAtS s) -> (n,(RawAtS s):l)
          ) (n,[]) raw
