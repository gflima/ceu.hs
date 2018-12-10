import qualified Text.Parsec           as T
import qualified Ceu.Parser.Stmt       as P
import qualified Ceu.Grammar.Globals   as G
import qualified Ceu.Grammar.Stmt      as S
import qualified Ceu.Grammar.Full.Eval as F
import qualified Ceu.Code.Gen          as C
import Ceu.Grammar.Ann.All

go :: String -> String
go input =
    let ret = T.parse (P.stmt <* T.eof) "" input in
        case ret of
            (Left  e)  -> show e
            (Right p1) -> let (es,p2) = F.compile' (True,True) p1 in
                case p2 of
                    (S.Nop _) -> show es
                    otherwise -> C.stmt p2

main :: IO ()
main = do
  s <- readFile "x.ceu"
  putStrLn $ go s
