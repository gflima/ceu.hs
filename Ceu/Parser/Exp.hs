module Ceu.Parser.Exp where

import Control.Applicative ((<|>))

import Text.Parsec.String (Parser)

import Ceu.Parser.Token (tk_num, tk_var, tk_minus)

import Ceu.Grammar.Globals (Exp(..))

expr_const :: Parser Exp
expr_const = do
    num <- tk_num
    return $ Const num

expr_read :: Parser Exp
expr_read = do
    str <- tk_var
    return $ Read str

expr_umn :: Parser Exp
expr_umn = do
    void <- tk_minus
    exp  <- expr
    return $ Umn exp

expr :: Parser Exp
expr = do
    e <- (expr_const <|> expr_read <|> expr_umn)
    return e


