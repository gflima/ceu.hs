module Ceu.Code.N where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann  (annz, Ann(..))
import Ceu.Grammar.Exp  (Exp(..), RawAt(..))
import Ceu.Grammar.Stmt (Stmt(..))

add :: Stmt -> Stmt
add p = p' where (_,_,p') = stmt 0 0 p

stmt :: Int -> Int -> Stmt -> (Int, Int, Stmt)

stmt n trl0 (Nop z) = (n+1,1, Nop z{nn=n,trails=(trl0,1)})

stmt n trl0 (Var z id tp p) =
    (n',ts', Var z{nn=n,trails=(trl0,ts')} id tp p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Inp z id p) =
    (n',ts', Inp z{nn=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Out z id p) =
    (n',ts', Out z{nn=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Evt z id p) =
    (n',ts', Evt z{nn=n,trails=(trl0,ts')} id p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Func z id tp p) =
    (n',ts', Func z{nn=n,trails=(trl0,ts')} id tp p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Write z var exp) =
    (n',1, Write z{nn=n,trails=(trl0,1)} var exp')
    where
        (n',exp') = expr (n+1) exp

stmt n trl0 (AwaitInp z ext) =
    (n+1,1, AwaitInp z{nn=n,trails=(trl0,1)} ext)

stmt n trl0 (EmitExt z ext Nothing) =
    (n+1,1, EmitExt z{nn=n,trails=(trl0,1)} ext Nothing)
stmt n trl0 (EmitExt z ext (Just exp)) =
    (n',1, EmitExt z{nn=n,trails=(trl0,1)} ext (Just exp'))
    where
        (n',exp') = expr (n+1) exp

stmt n trl0 (AwaitEvt z evt) =
    (n+1,1, AwaitEvt z{nn=n,trails=(trl0,1)} evt)

stmt n trl0 (EmitEvt z evt) =
    (n+1,1, EmitEvt z{nn=n,trails=(trl0,1)} evt)

stmt n trl0 (If z exp p1 p2) =
    (n2',mx, If z{nn=n,trails=(trl0,mx)} exp' p1' p2')
    where
        (n',exp')      = expr (n+1) exp
        (n1',ts1',p1') = stmt n'    trl0 p1
        (n2',ts2',p2') = stmt n1'   trl0 p2
        mx = max ts1' ts2'

stmt n trl0 (Seq z p1 p2) =
    (n2',mx, Seq z{nn=n,trails=(trl0,mx)} p1' p2')
    where
        (n1',ts2',p1') = stmt (n+1) trl0 p1
        (n2',ts1',p2') = stmt n1'   trl0 p2
        mx = max ts1' ts2'

stmt n trl0 (Loop z p) =
    (n',ts', Loop z{nn=n,trails=(trl0,ts')} p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Par z p1 p2) =
    (n2',sm, Par z{nn=n,trails=(trl0,sm)} p1' p2')
    where
        (n1',ts1',p1') = stmt (n+1) trl0        p1
        (n2',ts2',p2') = stmt n1'   (trl0+ts1') p2
        sm = ts1' + ts2'

stmt n trl0 (Trap z p) =
    (n',ts', Trap z{nn=n,trails=(trl0,ts')} p')
    where
        (n',ts',p') = stmt (n+1) trl0 p

stmt n trl0 (Escape z k) = (n+1, 1, Escape z{nn=n,trails=(trl0,1)} k)
stmt n trl0 (Halt z)     = (n+1, 1, Halt   z{nn=n,trails=(trl0,1)})
stmt n trl0 (RawS z raw) = (n',  1, RawS   z{nn=n,trails=(trl0,1)} raw')
    where
        (n',raw') = fold_raw (n+1) raw

stmt n trl0 p = error (show p)

-------------------------------------------------------------------------------

expr :: Int -> Exp -> (Int, Exp)
expr n (RawE  z raw)  = (n', RawE z{nn=n,trails=(0,0)} raw') where
                            (n',raw') = fold_raw (n+1) raw
expr n (Const z v)    = (n+1, Const z{nn=n,trails=(0,0)} v)
expr n (Read  z id)   = (n+1, Read  z{nn=n,trails=(0,0)} id)
expr n (Unit  z)      = (n+1, Unit  z{nn=n,trails=(0,0)})
expr n (Tuple z exps) = (n',  Tuple z{nn=n,trails=(0,0)} exps') where
                            (n',exps') = foldr (\e (n,l) ->
                                                let (n',e') = expr n e in
                                                    (n',e':l))
                                               (n+1,[]) exps

expr n (Call z1 id (Tuple z2 [e1,e2])) =
    (n2', Call z1{nn=n,trails=(0,0)} id
            (Tuple z2{nn=n+1,trails=(0,0)} [e1',e2']))
    where
        (n1',e1') = expr (n+2) e1
        (n2',e2') = expr n1'   e2
expr n (Call z id e) = (n', Call z{nn=n,trails=(0,0)} id e')
    where
        (n',e') = expr (n+1) e

-------------------------------------------------------------------------------

fold_raw :: Int -> [RawAt] -> (Int, [RawAt])
fold_raw n raw =
    foldr (\r (n,l) -> case r of
                        (RawAtE e) -> (n',(RawAtE e'):l) where (n',e') = expr n e
                        (RawAtS s) -> (n,(RawAtS s):l)
          ) (n,[]) raw
