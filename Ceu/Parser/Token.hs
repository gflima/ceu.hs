module Ceu.Parser.Token where

import Control.Monad (void)
import Data.Char (isLower, isLetter, isDigit)
import Control.Applicative (many)

import Text.Parsec.String            (Parser)
import Text.Parsec.String.Char       (oneOf, digit, satisfy, string)
import Text.Parsec.String.Combinator (many1)

s :: Parser ()
s = void $ many $ oneOf " \n\t"

tk_num :: Parser Int
tk_num = do
    s
    n <- many1 digit
    return (read n)

tk_var :: Parser String
tk_var = do
    s
    first <- satisfy isLower
    rest  <- many $ satisfy (\c -> isDigit c || isLetter c || c == '_')
    return (first:rest)

tk_int = tk_var

tk_escape = do
    s
    void <- string "escape"
    return ()
