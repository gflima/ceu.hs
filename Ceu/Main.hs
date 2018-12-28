import System.IO (hPutStrLn, stderr)
import System.Directory
import System.Process
import System.Exit
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

go :: Bool -> String -> [(String,Int)] -> Either String [(String,String)]
go o_encl src hst =
    case Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" src of
        (Left  e)  -> Left (show e)
        (Right p1) -> let (es,p2) = FullE.compile' (True,o_encl,True) p1
{-
        (Right p1) -> let (es,p2) = FullE.compile' (True,False)
                                        (FullG.Seq ann
                                            (FullG.Inp ann "FOREVER" False)
                                            p1)
-}
          in
            case p2 of
                (G.Nop _) -> Left  (show es)
                otherwise -> Right (Gen.stmt p2 hst)
          where
            ann = FullG.getAnn p1

main :: IO ()
main = do
    src <- readFile "x.ceu"
    tpl <- readFile "Ceu/Code/ceu.c"
    -- o_encl: False
    --let ret = go True src [("KEY",1),("KEY",2),("KEY",3),("KEY",4)] in
    case go True src [] of
        Left  err      -> hPutStrLn stderr err
        Right keypairs -> case Template.render keypairs tpl of
                            Left  err -> hPutStrLn stderr err
                            Right out -> writeFile "Ceu/Code/main/_ceu.c" out
    setCurrentDirectory "Ceu/Code/main/"
    ExitSuccess   <- system "gcc main.c"
    ExitFailure v <- system "./a.out"
    putStrLn $ ">>> " ++ (show v)
