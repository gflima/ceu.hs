import qualified Text.Parsec           as Parsec
import qualified Ceu.Parser.Token      as Token
import qualified Ceu.Parser.Stmt       as Parser
import qualified Ceu.Grammar.Stmt      as G
import qualified Ceu.Grammar.Full.Eval as Full
import qualified Ceu.Code.Gen          as Gen
import Ceu.Grammar.Ann.Source

go :: String -> (String,String)
go input =
    let ret = Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" input in
        case ret of
            (Left  e)  -> (show e, "")
            (Right p1) -> let (es,p2) = Full.compile' (True,True) p1 in
                case p2 of
                    (G.Nop _) -> (show es, "")
                    otherwise -> (show es, Gen.stmt p2)

main :: IO ()
main = do
  src <- readFile "x.ceu"
  putStrLn $ let (es,out) = go src in es++"\n\n"++out
