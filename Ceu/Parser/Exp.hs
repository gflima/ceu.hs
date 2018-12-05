module Ceu.Parser.Exp where

import Text.Parsec.Prim          ((<|>), getPosition)
import Text.Parsec.Pos           (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String        (Parser)
import Text.Parsec.Combinator    (chainl1)

import Ceu.Parser.Token (tk_num, tk_var, tk_str)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp (Exp(..))

toSource :: SourcePos -> Source
toSource pos = (sourceName pos, sourceLine pos, sourceColumn pos)

-------------------------------------------------------------------------------

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
    void <- tk_str "-"
    exp  <- expr
    return $ Umn exp

expr_parens :: Parser Exp
expr_parens = do
    void <- tk_str "("
    exp  <- expr
    void <- tk_str ")"
    return exp

expr_prim :: Parser Exp
expr_prim = (expr_const <|> expr_read <|> expr_umn <|> expr_parens)

-------------------------------------------------------------------------------

expr_add_sub :: Parser Exp
expr_add_sub = chainl1 expr_mul_div op where
    op = do
        void <- tk_str "+"
        return Add
     <|> do
        void <- tk_str "-"
        return Sub

expr_mul_div :: Parser Exp
expr_mul_div = chainl1 expr_prim op where
    op = do
        void <- tk_str "*"
        return Mul
     <|> do
        void <- tk_str "/"
        return Div

-------------------------------------------------------------------------------

expr :: Parser Exp
expr = do
    e <- expr_add_sub
    return e


