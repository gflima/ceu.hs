module Ceu.Parser.Exp where

import Debug.Trace

import Text.Parsec.Prim                 ((<|>), getPosition)
import Text.Parsec.Pos                  (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String               (Parser)
import Text.Parsec.String.Combinator    (chainl1)

import Ceu.Parser.Token (tk_num, tk_var, tk_str)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp (Exp(..), Exp'(..))

toSource :: SourcePos -> Source
toSource pos = (sourceName pos, sourceLine pos, sourceColumn pos)

-------------------------------------------------------------------------------

expr_const :: Parser Exp
expr_const = do
    pos <- getPosition
    num <- tk_num
    return $ Exp (Const num, toSource pos)

expr_read :: Parser Exp
expr_read = do
    pos <- getPosition
    str <- tk_var
    return $ Exp (Read str, toSource pos)

expr_umn :: Parser Exp
expr_umn = do
    pos <- getPosition
    void <- tk_str "-"
    exp  <- expr
    return $ Exp (Umn exp, toSource pos)

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
        pos  <- getPosition
        void <- tk_str "+"
        return (\op1 op2 -> Exp (Add op1 op2, toSource pos))
     <|> do
        pos  <- getPosition
        void <- tk_str "-"
        return (\op1 op2 -> Exp (Sub op1 op2, toSource pos))

expr_mul_div :: Parser Exp
expr_mul_div = chainl1 expr_prim op where
    op = do
        pos  <- getPosition
        void <- tk_str "*"
        return (\op1 op2 -> Exp (Mul op1 op2, toSource pos))
     <|> do
        pos  <- getPosition
        void <- tk_str "/"
        return (\op1 op2 -> Exp (Div op1 op2, toSource pos))

-------------------------------------------------------------------------------

expr :: Parser Exp
expr = do
    --v <- getPosition
    --trace (show v) $ return ()
    e <- expr_add_sub
    return e


