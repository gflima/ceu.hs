module Test.GenSpec (main) where

import Test.HUnit
import Debug.Trace
import System.IO (hPutStrLn, stderr)
import System.Directory
import System.Process
import System.Exit
import Control.Exception.Base

import qualified Text.Parsec              as Parsec
import qualified Ceu.Parser.Token         as Token
import qualified Ceu.Parser.Stmt          as Parser
import qualified Ceu.Grammar.Stmt         as G
import qualified Ceu.Grammar.Full.Eval    as FullE
import qualified Ceu.Grammar.Full.Grammar as FullG
import qualified Ceu.Code.Gen             as Gen
import qualified Ceu.Code.Template        as Template
import Ceu.Grammar.Ann.Source

ceuc :: String -> [(String,Int)] -> Either String [(String,String)]
ceuc src hst =
    let ret = Parsec.parse (Token.s *> Parser.stmt <* Parsec.eof) "" src in
        case ret of
            (Left  e)  -> Left (show e)
            (Right p1) -> let (es,p2) = FullE.compile' (True,True) p1
              in
                case p2 of
                    (G.Nop _) -> Left  (show es)
                    otherwise -> Right (Gen.stmt p2 hst)
              where
                ann = FullG.getAnn p1

go :: String -> String -> [(String,Int)] -> IO Int
go tpl src hst = do
    let ret = ceuc src hst in
        case ret of
            Left  err      -> hPutStrLn stderr err
            Right keypairs ->
                let ret = Template.render keypairs tpl in
                    case ret of
                        Left  err -> hPutStrLn stderr err
                        Right out -> writeFile "_ceu.c" out
    ExitSuccess   <- system "gcc main.c"
    ExitFailure v <- system "./a.out"
    return v

main :: IO ()
main = do
    tpl <- readFile "Ceu/Code/ceu.c"
    setCurrentDirectory "Ceu/Code/main/"
    mapM_ (\(ret1,hst,src) -> do
            ret2 <- go tpl src hst
            assertEqual "xxx" ret1 ret2
            )
          tests

-------------------------------------------------------------------------------

tests = [
    (10,  [], "escape 10"),
    (100, [], "escape 100"),
    (1,   [], "loop do break end ; escape 1"),
    (4, [("KEY",1)],
        unlines [
            "input  KEY   : int",
            "output PRINT : int",
            "",
            "var ret:int <- 1",
            "emit PRINT -> 0",
            "",
            "par/and do",
            "    await KEY",
            "    ret <- ret*2",
            "    emit PRINT -> 1",
            "with",
            "    await KEY",
            "    ret <- ret+2",
            "    emit PRINT -> 2",
            "end",
            "",
            "emit PRINT -> 3",
            "escape ret"
        ]),
    (6, [("KEY",1)],
        unlines [
            "output PRINT : int",
            "input  KEY   : int",
            "",
            "var ret : int <- 1",
            "",
            "par/or do",
            "    emit PRINT -> 0",
            "    await FOREVER;",
            "with",
            "    event e : int",
            "",
            "    par/and do",
            "        var k : int <- await e",
            "        emit PRINT -> k",
            "        ret <- ret + k",
            "    with",
            "        var k : int <- await KEY",
            "        emit e -> k+1",
            "        ret <- ret * 2",
            "        emit PRINT -> k",
            "    end",
            "end",
            "",
            "escape ret  // 6"
        ]),
    (10, [("KEY",1),("KEY",2),("KEY",3),("KEY",4)],
        unlines [
            "input  KEY   : int",
            "output PRINT : int",
            "var a:int <- await KEY",
            "emit PRINT -> a",
            "",
            "var ret:int <- a",
            "",
            "loop do",
            "    if 1 then",
            "        var a:int <- await KEY",
            "        ret <- ret + a",
            "        emit PRINT -> a",
            "    else",
            "        emit PRINT -> 0",
            "    end",
            "",
            "    emit PRINT -> ret",
            "    if ret == 10 then",
            "        break",
            "    end",
            "end",
            "",
            "escape ret"
        ])
 ]
