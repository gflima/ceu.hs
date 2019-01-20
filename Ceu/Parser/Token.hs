module Ceu.Parser.Token where

import Control.Monad (void, guard)
import Data.Char (isLower, isUpper)

import Text.Parsec.Prim       (many, (<|>), (<?>), try)
import Text.Parsec.String     (Parser)
import Text.Parsec.Char       (char, oneOf, digit, satisfy, string, letter, anyChar, newline)
import Text.Parsec.Combinator (many1, notFollowedBy, manyTill, eof)

types = [
    "Int"
  ]

keywords = [
    "do",
    "else",
    "else/if",
    "end",
    "for",
    "func",
    "if",
    "instance",
    "loop",
    "of",
    "set",
    "then",
    "var",
    "return",
    "type",
    "typeclass",
    "with"
  ]
tk_reserved :: Parser ()
tk_reserved = do
    void <- foldr1 (<|>) (map tk_key keywords)
    return ()

s :: Parser ()
s = void $ many $ (void $ oneOf " ;\n\t") <|> comm

comm :: Parser ()
comm = void $ try $ (string "//" >> (manyTill anyChar (void newline<|>eof)) <?> "")

tk_str :: String -> Parser ()
tk_str str = do
    n <- string str
    s
    return ()

tk_op :: Parser String
tk_op = do
    --void <- notFollowedBy (tk_str "<-" <|> tk_str "->")
    op   <- many1 $ oneOf "!@#$%&*-+=/?^~\\|<>"
    guard $ op /= "<-" && op /= "->"
    s
    return $ op

tk_num :: Parser Int
tk_num = do
    n <- many1 digit
    s
    return (read n)

tk_var :: Parser String     -- x, x_0       // Xx
tk_var = do
    --void  <- notFollowedBy tk_reserved
    first <- satisfy isLower
    rest  <- many $ (digit <|> letter <|> char '_')
    guard $ not $ elem (first:rest) keywords
    s
    return (first:rest)

tk_func = tk_var

tk_type :: Parser String    -- Int, Int_0   // I, II, int, _Int
tk_type = do
    first <- satisfy isUpper
    rest  <- many1 $ (digit <|> letter <|> char '_')
    guard $ not $ null $ filter (\c -> isLower c) rest
    s
    return (first:rest)

tk_key :: String -> Parser String
tk_key k = do
    key  <- string k
    void <- notFollowedBy (letter <|> char '_' <|> digit)
    guard $ elem key keywords
    s
    return key
