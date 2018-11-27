module Ceu.Parser.Token where

import Control.Monad (void)
import Data.Char (isLower, isLetter, isDigit)
import Control.Applicative (many)

import Text.Parsec.String            (Parser)
import Text.Parsec.String.Char       (char, oneOf, digit, satisfy, string)
import Text.Parsec.String.Combinator (many1)

s :: Parser ()
s = void $ many $ oneOf " \n\t"

tk_parens_open :: Parser ()
tk_parens_open = do
    n <- char '('
    s
    return ()

tk_parens_close :: Parser ()
tk_parens_close = do
    n <- char ')'
    s
    return ()

tk_minus :: Parser ()
tk_minus = do
    n <- char '-'
    s
    return ()

tk_num :: Parser Int
tk_num = do
    n <- many1 digit
    s
    return (read n)

tk_var :: Parser String
tk_var = do
    first <- satisfy isLower
    rest  <- many $ satisfy (\c -> isDigit c || isLetter c || c == '_')
    s
    return (first:rest)

tk_int = tk_var

tk_escape :: Parser ()
tk_escape = do
    void <- string "escape"
    s
    return ()
