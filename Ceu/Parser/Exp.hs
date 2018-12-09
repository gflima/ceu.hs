module Ceu.Parser.Exp where

import Text.Parsec.Prim          ((<|>), getPosition)
import Text.Parsec.Pos           (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String        (Parser)
import Text.Parsec.Combinator    (chainl1)

import Ceu.Parser.Token (tk_num, tk_var, tk_str)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp (Exp(..))

pos2src :: SourcePos -> Source
pos2src pos = (sourceName pos, sourceLine pos, sourceColumn pos)

-------------------------------------------------------------------------------

expr_const :: Parser (Exp Source)
expr_const = do
    pos <- getPosition
    num <- tk_num
    return $ Const (pos2src pos) num

expr_read :: Parser (Exp Source)
expr_read = do
    pos <- getPosition
    str <- tk_var
    return $ Read (pos2src pos) str

expr_umn :: Parser (Exp Source)
expr_umn = do
    pos  <- getPosition
    void <- tk_str "-"
    exp  <- expr
    return $ Umn (pos2src pos) exp

expr_parens :: Parser (Exp Source)
expr_parens = do
    void <- tk_str "("
    exp  <- expr
    void <- tk_str ")"
    return exp

expr_prim :: Parser (Exp Source)
expr_prim = (expr_const <|> expr_read <|> expr_umn <|> expr_parens)

-------------------------------------------------------------------------------

expr_add_sub :: Parser (Exp Source)
expr_add_sub = chainl1 expr_mul_div op where
    op = do
        pos  <- getPosition
        void <- tk_str "+"
        return (\a b -> Add (pos2src pos) a b)
     <|> do
        pos  <- getPosition
        void <- tk_str "-"
        return (\a b -> Sub (pos2src pos) a b)

expr_mul_div :: Parser (Exp Source)
expr_mul_div = chainl1 expr_prim op where
    op = do
        pos  <- getPosition
        void <- tk_str "*"
        return (\a b -> Mul (pos2src pos) a b)
     <|> do
        pos  <- getPosition
        void <- tk_str "/"
        return (\a b -> Div (pos2src pos) a b)

-------------------------------------------------------------------------------

expr :: Parser (Exp Source)
expr = do
    e <- expr_add_sub
    return e
