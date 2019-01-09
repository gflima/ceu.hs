import Test.HUnit
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
import qualified Ceu.Code.Gen             as Gen
import qualified Ceu.Code.Template        as Template
import Ceu.Grammar.Globals (Errors)

ceuc :: String -> [(String,Int)] -> (Errors, Maybe [(String,String)])
ceuc src hst =
    case Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" src of
        (Left  e)    -> ([show e], Nothing)
        (Right full) -> (es, out) where
                            (es,basic) = FullE.compile' (True,True,True) full
                            out = if null es then
                                    Just $ Gen.stmt (traceShowId basic) hst
                                  else
                                    Nothing

go :: String -> String -> [(String,Int)] -> IO (Int,Errors)
go tpl src hst =
    case keypairs of
        Just kps ->
            case Template.render kps tpl of
                Left  err -> return (0,[err])
                Right out -> do
                    writeFile "_ceu.c" out
                    ExitSuccess   <- system "gcc main.c"
                    ExitFailure v <- system "./a.out"
                    return (v,es)
        Nothing -> do
            return (0,es)
    where
        (es,keypairs) = ceuc src hst


main :: IO ()
main = do
    src <- readFile "Ceu/Code/x.ceu"
    tpl <- readFile "Ceu/Code/ceu.c"
    setCurrentDirectory "Ceu/Code/main/"
    (ret,es) <- go tpl src []
    assertEqual "error" [] es
    print (show ret)
    return ()
