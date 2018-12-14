import System.IO (hPutStrLn, stderr)
import Debug.Trace

import qualified Text.Parsec              as Parsec
import qualified Ceu.Parser.Token         as Token
import qualified Ceu.Parser.Stmt          as Parser
import qualified Ceu.Grammar.Stmt         as G
import qualified Ceu.Grammar.Full.Eval    as FullE
import qualified Ceu.Grammar.Full.Grammar as FullG
import qualified Ceu.Code.Gen             as Gen
import qualified Ceu.Code.Template        as Template
import Ceu.Grammar.Ann.Source

go :: String -> Either String [(String,String)]
go input =
    let ret = Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" input in
        case ret of
            (Left  e)  -> Left (show e)
            (Right p1) -> let (es,p2) = FullE.compile' (True,False)
                                            (FullG.Seq ann
                                                (FullG.Inp ann "FOREVER" False)
                                                p1)
              in
                case p2 of
                    (G.Nop _) -> Left  (show es)
                    otherwise -> Right (Gen.stmt p2)
              where
                ann = FullG.getAnn p1

main :: IO ()
main = do
    src <- readFile "x1.ceu"
    tpl <- readFile "Ceu/Code/ceu.c"
    let ret = go src in
        case ret of
            Left  err      -> hPutStrLn stderr err
            Right keypairs ->
                let ret = Template.render keypairs tpl in
                    case ret of
                        Left  err -> hPutStrLn stderr err
                        Right out -> writeFile "Ceu/Code/main/_ceu.c" out
