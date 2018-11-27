module Ceu.Parser.Exp where

import Text.Parsec.String (Parser)

import Ceu.Parser.Token (tk_num)

import Ceu.Grammar.Globals (Exp(..))

expr_const = do
    v <- tk_num
    return $ Const v

expr :: Parser Exp
expr = do
    e <- expr_const
    return e


