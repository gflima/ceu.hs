module Ceu.Parser.Exp where

import Control.Applicative ((<|>))

import Text.Parsec.String (Parser)
import Text.Parsec.String.Combinator (chainl1)

import Ceu.Parser.Token (tk_num, tk_var, tk_minus, tk_char)

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

expr_parens :: Parser Exp
expr_parens = do
    void <- tk_char '('
    exp  <- expr
    void <- tk_char ')'
    return exp

expr_prim :: Parser Exp
expr_prim = (expr_const <|> expr_read <|> expr_umn <|> expr_parens)

-------------------------------------------------------------------------------

expr_add_sub :: Parser Exp
expr_add_sub = chainl1 expr_mul_div op where
    op = do
        void <- tk_char '+'
        return Add
     <|> do
        void <- tk_char '-'
        return Sub

expr_mul_div :: Parser Exp
expr_mul_div = chainl1 expr_prim op where
    op = do
        void <- tk_char '*'
        return Mul
     <|> do
        void <- tk_char '/'
        return Div

-------------------------------------------------------------------------------

expr :: Parser Exp
expr = do
    e <- expr_add_sub
    return e


