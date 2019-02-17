module Ceu.Parser.Token where

import Control.Monad          (void, guard, when)
import Data.Char              (isLower, isUpper)
import Data.List              (intercalate)

import Text.Parsec.Prim       (many, (<|>), (<?>), try, unexpected)
import Text.Parsec.String     (Parser)
import Text.Parsec.Char       (char, oneOf, digit, satisfy, string, letter, anyChar, newline)
import Text.Parsec.Combinator (many1, notFollowedBy, manyTill, eof)

keywords = [
    "_",
    "do",
    "else",
    "else/if",
    "end",
    "error",
    "extends",
    "for",
    "func",
    "if",
    "loop",
    "set",
    "set!",
    "then",
    "var",
    "return",
    "type",
    "type/class",
    "type/instance",
    "with"
  ]
tk_reserved :: Parser ()
tk_reserved = do
    void <- foldr1 (<|>) (map tk_key keywords)
    return ()

s :: Parser ()
s = void $ many $ (void $ oneOf " ;\n\t") <|> comm

comm :: Parser ()
comm = void $ ((try $ string "//") >> (manyTill anyChar (void newline<|>eof)) <?> "")

tk_sym :: String -> Parser ()
tk_sym str = do
    void <- string str
    s
    return ()

tk_op :: Parser String
tk_op = do
    --void <- notFollowedBy (tk_sym "<-" <|> tk_sym "->")
    op   <- many1 $ (oneOf "!@#$%&*-+=/?^~\\|<>" <?> "operator")
    --guard $ op /= "<-" && op /= "->"
    when (op == "<-" || op == "->") $ unexpected "arrow"
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
    rest  <- many $ (digit <|> letter <|> oneOf "_'?" <?> "identifier")
    when (elem (first:rest) keywords) $ unexpected $ "`" ++ (first:rest) ++ "`"
    s
    return (first:rest)

tk_func = tk_var

tk_type :: Parser String    -- Int, Int_0   // I, II, int, _Int
tk_type = do
    first <- satisfy isUpper
    rest  <- many1 $ (digit <|> letter <|> char '_' <?> "type identifier")
    --guard $ not $ null $ filter (\c -> isLower c) rest
    when (all isUpper rest) $ unexpected "uppercase identifier"
    s
    return (first:rest)

tk_key :: String -> Parser String
tk_key k = do
    key  <- string k
    void <- notFollowedBy (letter <|> char '_' <|> digit)
    guard $ elem key keywords
    s
    return key
