module Ceu.Parser.Token where

import Control.Monad (void, guard)
import Data.Char (isLower, isLetter, isDigit)

import Text.Parsec.Prim              (many, (<|>))
import Text.Parsec.String            (Parser)
import Text.Parsec.String.Char       (char, oneOf, digit, satisfy, string, letter)
import Text.Parsec.String.Combinator (many1, notFollowedBy)

types = [
    "int"
  ]

keywords = [
    "do",
    "escape",
    "end",
    "var"
  ]
tk_reserved :: Parser ()
tk_reserved = foldr1 (<|>) (map tk_key keywords)

s :: Parser ()
s = void $ many $ oneOf " ;\n\t"

tk_str :: String -> Parser ()
tk_str str = do
    n <- string str
    s
    return ()

tk_num :: Parser Int
tk_num = do
    n <- many1 digit
    s
    return (read n)

tk_var :: Parser String
tk_var = do
    --void  <- notFollowedBy tk_reserved
    first <- satisfy isLower
    rest  <- many $ (digit <|> letter <|> char '_')
    guard $ not $ elem (first:rest) (keywords++types)
    s
    return (first:rest)

tk_int = tk_var

tk_type :: Parser String
tk_type = do
    first <- satisfy isLower
    rest  <- many $ (digit <|> letter <|> char '_')
    guard $ elem (first:rest) types
    s
    return (first:rest)

tk_key :: String -> Parser ()
tk_key k = do
    key  <- string k
    void <- notFollowedBy (letter <|> char '_' <|> digit)
    guard $ elem key keywords
    s
    return ()
