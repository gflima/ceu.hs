module Ceu.Parser.Stmt where

import Control.Monad                    (guard)

import Text.Parsec.Prim                 ((<|>), try)
import Text.Parsec.String               (Parser)
import Text.Parsec.String.Combinator    (chainr1, optionMaybe)

import Ceu.Parser.Token                 (tk_key, tk_var, tk_type, tk_str)
import Ceu.Parser.Exp                   (expr)

import Ceu.Grammar.Full.Grammar         (Stmt(..))

-------------------------------------------------------------------------------

stmt_nop :: Parser Stmt
stmt_nop = do
    return $ Nop

stmt_escape :: Parser Stmt
stmt_escape = do
    void <- tk_key "escape"
    e    <- expr
    return $ Escape Nothing (Just e)

stmt_var :: Parser Stmt
stmt_var = do
    void <- tk_key "var"
    tp   <- tk_type
    var  <- tk_var
    guard $ tp == "int"         -- TODO
    exp  <- optionMaybe $ (tk_str "<-") *> expr
    return $ Var var exp Nothing

stmt_write :: Parser Stmt
stmt_write = do
    var  <- tk_var
    void <- tk_str "<-"
    exp  <- expr
    return $ Write var exp

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
    stmt <- try stmt_escape <|> try stmt_do <|> try stmt_var <|> try stmt_write
    return stmt

stmt_seq :: Parser Stmt
stmt_seq = chainr1 stmt1 (do return Seq) where

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

