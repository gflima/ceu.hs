import System.IO (hPutStrLn, stderr)
import Debug.Trace

import qualified Text.Parsec           as Parsec
import qualified Ceu.Parser.Token      as Token
import qualified Ceu.Parser.Stmt       as Parser
import qualified Ceu.Grammar.Stmt      as G
import qualified Ceu.Grammar.Full.Eval as Full
import qualified Ceu.Code.Gen          as Gen
import qualified Ceu.Code.Template     as Template
import Ceu.Grammar.Ann.Source

go :: String -> Either String String
go input =
    let ret = Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" input in
        case ret of
            (Left  e)  -> Left (show e)
            (Right p1) -> let (es,p2) = Full.compile' (True,True) p1 in
                case p2 of
                    (G.Nop _) -> Left  (show es)
                    otherwise -> Right (Gen.stmt p2)

main :: IO ()
main = do
    src <- readFile "x1.ceu"
    tpl <- readFile "Ceu/Code/ceu.c"
    let ret = go src in
        case ret of
            Left  err -> hPutStrLn stderr err
            Right out ->
                let ret = Template.render [("CEU_CODES",out)] tpl in
                    case ret of
                        Left  err -> hPutStrLn stderr err
                        Right out -> writeFile "Ceu/Code/env/_ceu_app.c.h" out
