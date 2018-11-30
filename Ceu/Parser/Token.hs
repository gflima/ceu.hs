module Ceu.Parser.Token where

import Control.Monad (void)
import Control.Applicative (many, (<|>))
import Data.Char (isLower, isLetter, isDigit)

import Text.Parsec.Prim              (try)
import Text.Parsec.String            (Parser)
import Text.Parsec.String.Char       (char, oneOf, digit, satisfy, string, letter)
import Text.Parsec.String.Combinator (many1, notFollowedBy)

s :: Parser ()
s = void $ many $ oneOf " \n\t"

tk_char :: Char -> Parser ()
tk_char c = do
    n <- char c
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
    rest  <- many $ (digit <|> letter <|> char '_')
    s
    return (first:rest)

tk_int = tk_var

tk_key :: String -> Parser ()
tk_key k = try $ do
    i    <- string k
    void <- notFollowedBy (letter <|> char '_' <|> digit)
    s
    return ()
