module Ceu.Parser.Stmt where

import Control.Applicative ((<|>))

import Text.Parsec.String (Parser)

import Ceu.Parser.Token (tk_key)
import Ceu.Parser.Exp   (expr)

import Ceu.Grammar.Full.Grammar (Stmt(..))

stmt_nop :: Parser Stmt
stmt_nop = do
    return $ Nop

stmt_escape :: Parser Stmt
stmt_escape = do
    void <- tk_key "escape"
    e    <- expr
    return $ Escape Nothing (Just e)

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
    stmt <- stmt_escape <|> stmt_do
    return stmt

stmt_seq :: Parser Stmt
stmt_seq = do
    p1 <- stmt1
    p2 <- stmt <|> stmt_nop
    return $ Seq p1 p2

stmt_do :: Parser Stmt
stmt_do = do
    void <- tk_key "do"
    p    <- stmt <|> stmt_nop
    void <- tk_key "end"
    return $ Scope p

stmt :: Parser Stmt
stmt = do
    s <- stmt_seq
    return s

