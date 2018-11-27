module Ceu.Parser.Stmt where

import Text.Parsec.String (Parser)

import Ceu.Parser.Token (tk_escape)
import Ceu.Parser.Exp   (expr)

import Ceu.Grammar.Full.Grammar (Stmt(..))

stmt_escape :: Parser Stmt
stmt_escape = do
    void <- tk_escape
    e    <- expr
    return $ Escape Nothing (Just e)

stmt :: Parser Stmt
stmt = do
    s <- stmt_escape
    return s

