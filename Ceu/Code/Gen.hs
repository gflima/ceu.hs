module Ceu.Code.Gen where

import Debug.Trace
import Ceu.Grammar.Exp  (Exp(..))
import Ceu.Grammar.Stmt (Stmt(..))

data State = State { iden  :: Int
                   , spc   :: String
                   , traps :: [Int]
                   } -- deriving (Show)   

cmd :: String -> String
cmd str = str ++ ";\n"

expr :: Exp ann -> String
expr (Const _ n) = show n

stmt :: (Show ann) => Stmt ann -> String
stmt p = aux g p --(traceShowId p)
        where
            g = State { iden  = 0
                      , spc   = "  "
                      , traps = []
                      }

aux :: State -> Stmt ann -> String
aux g (Var      _ var p)     = aux g p
aux g (Write    _ var e)     = cmd $ (spc g) ++ "CEU_APP.root." ++ var ++ " = " ++ (expr e)
aux g (AwaitExt _ "FOREVER") = cmd $ (spc g) ++ "return"
aux g (Seq      _ p1 p2)     = (aux g p1) ++ (aux g p2)
aux g (Trap     _ p)         = cmd $ (aux g' p) ++ "case Trap_" ++ (show $ iden g) ++ ":"
                               where
                                g' = g { iden  = (iden g)+1
                                       , traps = (iden g):(traps g)
                                       }
aux g (Escape _ k)           = cmd $ (spc g) ++ "CEU_GOTO(Trap_" ++ (show $ (traps g)!!k) ++ ")"
