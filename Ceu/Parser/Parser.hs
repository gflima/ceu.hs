module Ceu.Parser.Parser where

import Prelude hiding (exp)
import Control.Monad (void)
import Data.Char (isLower, isLetter, isDigit)
import Control.Applicative ((<|>), many)

import Text.Parsec.String (Parser)
import Text.Parsec.String.Char (oneOf, char, digit, satisfy, string)
import Text.Parsec.String.Combinator (many1, choice, chainl1)

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

s :: Parser ()
s = void $ many $ oneOf " \n\t"

num :: Parser Int
num = do
    s
    n <- many1 digit
    return (read n)

id_var :: Parser String
id_var = do
    s
    first <- satisfy isLower
    rest  <- many $ satisfy (\c -> isDigit c || isLetter c || c == '_')
    return (first:rest)

id_int = id_var

exp_const = do
    v <- num
    return $ Const v

exp :: Parser Exp
exp = do
    e <- exp_const
    return e

stmt_escape :: Parser Stmt
stmt_escape = do
    void <- string "escape"
    e    <- exp
    return $ Escape Nothing (Just e)

stmt :: Parser Stmt
stmt = do
    s <- stmt_escape
    return s
