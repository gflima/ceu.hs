module Test.GenSpec (main) where

import Test.HUnit
import Debug.Trace
import System.Directory
import System.Process
import System.Exit
import Control.Exception.Base

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
                                    Just $ Gen.stmt basic hst
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
    tpl <- readFile "Ceu/Code/ceu.c"
    setCurrentDirectory "Ceu/Code/main/"
    mapM_ (\(ret1,es1,hst,src) -> do
            (ret2,es2) <- go tpl src hst
            assertEqual src es1  es2
            assertEqual src ret1 ret2
            )
          tests

-------------------------------------------------------------------------------

tests :: [(Int, Errors, [(String,Int)], String)]
tests = [
  --(0,   [], [], "xXxXxXxXxXxXxXxXxXxXx"),    -- (to force error)
--
    (10,  [], [], "escape 10"),
    (10,  [], [], "escape 5+5"),
    (100, [], [], "escape 100"),
    (100, [], [], "escape {100}"),
    (1,   [], [], "escape {CEU_TRAILS_N}"),
    (16,  [], [], "escape {sizeof(tceu_trl)}"),
    (24,  [], [], "escape {sizeof(tceu_mem_ROOT)}"),
    (0,   ["(line 1, column 18):\ntypes do not match : Int :> ()"], [],
                  "val x :Int set x <- () escape 100"),
    (0,   ["(line 1, column 11):\ntypes do not match : Int :> ()"], [],
                  "val x: Int<- () escape 100"),
    (100, [], [], "val x:() set x <- () escape 100"),
    (100, [], [], "val x:Int <- 100 escape x"),
    (100, [], [], "{int x = 100}; escape {x}"),
    (100, [], [], "val x:Int <- 100 escape {`x`}"),
    (3,   [], [], "val x:Int<-1 ; val y:Int<-2 ; escape {`x+y`}"),
    (0,   ["(line 1, column 15):\ntypes do not match : ((),()) :> ()"], [],
                  "val x:((),()) <- () val y:Int <- 1 escape y"),
    (1,   [], [], "val x:((),()) <- ((),()) val y:Int <- 1 escape y"),
    (3,   [], [], "val x:(Int,Int)<-(1,2) ; escape '+x"),
    (10,  [], [], "val vs:(Int,Int) <- (5,5) ; escape '+ vs"),
-- if
    (10,  [], [], "if 1==1 then else end escape 10"),
    (0,   ["(line 1, column 21):\ntypes do not match : (a,a) :> (((),()),())"],
            [],
            "val x:((),()) ; if x==() then escape 100 else escape 0 end"),
    -- TODO: unused vars
    (24,  [], [], "val x:Int ; val y:Int ; escape {sizeof(tceu_mem_ROOT)}"),
    (27,  [], [], "val x:Int<-1 ; val y:Int<-2 ; escape {`(x+y)`+sizeof(tceu_mem_ROOT)}"),
    (1,   [], [], "if 1==1 then escape 1 else escape 0 end"),
    (100, [], [], "val x:() <- () if x==() then escape 100 else escape 0 end"),
    (0,   ["(line 1, column 1):\n`loop` never iterates"],
            [],
            "loop do if 1==1 then break else await FOREVER end end ; escape 1"),
    (0,   ["(line 1, column 1):\n`loop` never iterates"],
        [],
        "loop do break end ; escape 1"),
-- pattern matching
    (55,  [], [], "mut x:Int; val y:(Int,Int) <- (3,55); set ((_,x),_)<-(y,1); escape x"),
    (100, [], [], "val x:((),()) <- ((),()) ; val x1:() ; set (x1,_)<-x  if x1==() then escape 100 else escape 0 end"),
    (3,   [], [], "val (x,y):(Int,Int) <- (1, 2); escape x+y"),
    (3,   [], [], "mut (x, (y,_)) : (Int, (Int,Int)) <- (1, (2,3)); escape x+y"),
-- trap/escape()
    (1,   [], [], "val void:() <- trap do escape () end ; escape 1"),
    -- TODO: escape x@1 + x@2
    (2,   [], [], "val x:((),Int) <- trap do escape ((),2) end ; val (_,y):((),Int) <- x ; escape y"),
    (1,   [], [],
        unlines [
            "mut ret:Int <- 1",
            "val x:() <- trap do",
            "   trap do",
            "       if 1==1 then",
            "           escape/x",
            "       end",
            "       set ret <- 99",
            "       escape ()",
            "   end",
            "   escape/x",
            "end",
            "escape ret"
        ]),
-- funcs
    (1,   [], [], "func f : (Int -> Int); escape 1"),
    (0,   ["(line 1, column 32):\nunexpected \"e\"\nmissing arguments"],
            [],
            "func f : (Int -> Int) do end ; escape 1"),
    (0,   ["(line 1, column 8):\nfunction 'f' is not declared"],
            [],
            "escape f 1"),
    (0, ["(line 1, column 1):\nterminating `trap` body","(line 1, column 1):\nmissing `escape` statement"],
        [], "func f : v : (Int -> Int) do end ; escape 1"),
    (1, [], [], "func f : v : (Int -> Int) do escape 0 end ; escape 1"),
    (2, [], [], "func f : v : (Int -> Int) do escape v+1 end ; escape f 1"),
    -- TODO: ((f 1)._1 , (f 1)._2)
    (3, [], [],
        unlines [
            "func f : v : (Int -> (Int,Int)) do",
            "   escape (v,v+1)",
            "end",
            "val (x,y):(Int,Int) <- f 1",
            "val z:(Int,Int) <- (x,y)",
            "escape '+ z"
        ]),
    (1, [],
        [],
        unlines [
            "func f : (Int -> Int)",
            "func f : (Int -> Int)",
            "escape 1"
        ]),
    (0, ["(line 2, column 1):\ntypes do not match : (Int -> Int) :> (Int -> ())"],
        [],
        unlines [
            "func f : (Int -> Int)",
            "func f : a : (Int -> ()) do escape end",
            "escape 0"
        ]),
    (2, [],
        [],
        unlines [
            "func f : (Int -> Int)",
            "func f : a : (Int -> Int) do escape a+1 end",
            "escape f 1"
        ]),
-- await
    (35, [], [("KEY",1)],
        unlines [
            "input KEY:Int",
            "val y:Int <- 2",
            "mut x:Int <- 0",
            "set x <- await KEY",
            "escape {`x` + `y` + sizeof(tceu_mem_ROOT)}"
        ]),
    (27, [], [("KEY",1)],
        unlines [
            "input KEY:Int",
            "val x:Int <- await KEY",
            "val y:Int <- 2",
            "escape {`x` + `y` + sizeof(tceu_mem_ROOT)}"
        ]),
-- emit/await
    (1, [], [],
        unlines [
            "event e : ()",
            "par/and do",
            "   await e",
            "with",
            "   emit e",
            "end",
            "escape 1"
        ]),
-- par
    (10,  [], [], "par/and do with end ; escape 10"),
    (4, [], [("KEY",1)],
        unlines [
            "input  KEY   : Int",
            "output PRINT : Int",
            "",
            "mut ret:Int <- 1",
            "emit PRINT <- 0",
            "",
            "par/and do",
            "    await KEY",
            "    set ret <- ret*2",
            "    emit PRINT <- 1",
            "with",
            "    await KEY",
            "    set ret <- ret+2",
            "    emit PRINT <- 2",
            "end",
            "",
            "emit PRINT <- 3",
            "escape ret"
        ]),
    (6, [], [("KEY",1)],
        unlines [
            "output PRINT : Int",
            "input  KEY   : Int",
            "",
            "mut ret : Int <- 1",
            "",
            "par/or do",
            "    emit PRINT <- 0",
            "    await FOREVER;",
            "with",
            "    event e : Int",
            "",
            "    par/and do",
            "        val k : Int <- await e",
            "        emit PRINT <- k",
            "        set ret <- ret + k",
            "    with",
            "        val k : Int <- await KEY",
            "        emit e <- k+1",
            "        set ret <- ret * 2",
            "        emit PRINT <- k",
            "    end",
            "end",
            "",
            "escape ret  // 6"
        ]),
    (10, [],
        [("KEY",0),("KEY",1),("KEY",0),("KEY",2),("KEY",0),("KEY",3),("KEY",0),("KEY",4),("KEY",0)],
        unlines [
            "input  KEY   : Int",
            "output PRINT : Int",
            "val a:Int <- await KEY",
            "emit PRINT <- a",
            "",
            "mut ret:Int <- a",
            "",
            "loop do",
            "    if 1==1 then",
            "        val a1:Int <- await KEY",
            "        set ret <- ret + a1",
            "        emit PRINT <- a1",
            "        emit PRINT <- ret",
            "    else",
            "        emit PRINT <- 0",
            "    end",
            "",
            "    emit PRINT <- ret",
            "    if ret == 10 then",
            "        break",
            "    end",
            "    await KEY",
            "end",
            "",
            "escape ret"
        ]),
    (4, [], [("KEY",0)],
        unlines [
            "input  KEY   : Int",
            "output PRINT : Int",
            "emit PRINT <- 0",
            "",
            "mut ret : Int <- 1",
            "",
            "par/and do",
            "    await KEY",
            "    emit PRINT <- 1",
            "    set ret <- ret+1",
            "with",
            "    emit PRINT <- 2",
            "    await KEY",
            "    set ret <- ret*2",
            "end",
            "",
            "emit PRINT <- 3",
            "escape ret"
        ]),
    (1, [], [("KEY",0)],
        unlines [
            "input  KEY   : Int",
            "output PRINT : Int",
            "emit PRINT <- 0",
            "",
            "trap do",
            "    await KEY;",
            "    escape ();",
            "end",
            "",
            "emit PRINT <- 1",
            "escape 1"
        ]),
    (4, [], [("KEY",0)],
        unlines [
            "input  KEY   : Int",
            "output PRINT : Int",
            "emit PRINT <- 0",
            "",
            "mut ret : Int <- 1",
            "",
            "par/or do",
            "    emit PRINT <- 1",
            "    par/or do",
            "        emit PRINT <- 11",
            "        set ret <- ret + 1",
            "    with",
            "        emit PRINT <- 12",
            "        set ret <- 0",
            "    end",
            "    emit PRINT <- 2",
            "    await KEY",
            "    emit PRINT <- 3",
            "    set ret <- ret * 5",
            "with",
            "    emit PRINT <- 99",
            "    set ret <- ret + 2",
            "end",
            "",
            "emit PRINT <- 4",
            "escape ret"
        ])
 ]
