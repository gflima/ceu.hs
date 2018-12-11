module Ceu.Code.N where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))

add :: (Stmt Source) -> (Stmt All)
add p = p' where (_,p') = stmt 0 p

stmt :: Int -> (Stmt Source) -> (Int, Stmt All)

stmt n (Nop src) = (n, Nop All{source=src,n=n})

stmt n (Var src var p) =
    (n', Var All{source=src,n=n} var p')
    where
        (n',p') = stmt (n+1) p

stmt n (Write src var exp) =
    (n', Write All{source=src,n=n} var exp')
    where
        (n',exp') = expr (n+1) exp

stmt n (AwaitExt src ext) =
    (n, AwaitExt All{source=src,n=n} ext)

stmt n (EmitExt src ext Nothing) =
    (n, EmitExt All{source=src,n=n} ext Nothing)
stmt n (EmitExt src ext (Just exp)) =
    (n', EmitExt All{source=src,n=n} ext (Just exp'))
    where
        (n',exp') = expr (n+1) exp

stmt n (If src exp p1 p2) =
    (n2', If All{source=src,n=n} exp' p1' p2')
    where
        (n',exp') = expr (n+1)   exp
        (n1',p1') = stmt (n'+1)  p1
        (n2',p2') = stmt (n1'+1) p2

stmt n (Seq src p1 p2) =
    (n2', Seq All{source=src,n=n} p1' p2')
    where
        (n1',p1') = stmt (n+1)   p1
        (n2',p2') = stmt (n1'+1) p2

stmt n (Loop src p) =
    (n', Loop All{source=src,n=n} p')
    where
        (n',p') = stmt (n+1) p

stmt n (Par src p1 p2) =
    (n2', Par All{source=src,n=n} p1' p2')
    where
        (n1',p1') = stmt (n+1)   p1
        (n2',p2') = stmt (n1'+1) p2

stmt n (Trap src p) =
    (n', Trap All{source=src,n=n} p')
    where
        (n',p') = stmt (n+1) p

stmt n (Escape src k) =
    (n, Escape All{source=src,n=n} k)

expr :: Int -> (Exp Source) -> (Int, Exp All)
expr n (Const src v) = (n+1, Const All{source=src,n=n} v)
