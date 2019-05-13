module Ceu.Parser.Token where

import Control.Monad          (void, guard, when)
import Data.Char              (isLower, isUpper)
import Data.List              (intercalate)

import Ceu.Grammar.Globals    (ID_Data_Hier)

import Text.Parsec.Prim       (many, (<|>), (<?>), try, unexpected)
import Text.Parsec.String     (Parser)
import Text.Parsec.Char       (char, oneOf, digit, satisfy, string, letter, anyChar, newline)
import Text.Parsec.Combinator (many1, notFollowedBy, manyTill, eof)

keywords = [
    "_",
    "call",
    "data",
    "do",
    "else",
    "else/if",
    "end",
    "error",
    "extends",
    "for",
    "func",
    "if",
    "implementation",
    "implements",
    "interface",
    "loop",
    "of",
    "set",
    "set!",
    "then",
    "var",
    "return",
    "where",
    "with"
  ]
tk_reserved :: Parser ()
tk_reserved = do
    void <- foldr1 (<|>) (map tk_key keywords)
    return ()

s :: Parser ()
s = void $ many $ (void $ oneOf " ;\n\t") <|> comm

tk_spc :: Parser ()
tk_spc = s

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
    fst <- satisfy isLower
    rst <- many $ (digit <|> letter <|> oneOf "_'?" <?> "identifier")
    when (elem (fst:rst) keywords) $ unexpected $ "`" ++ (fst:rst) ++ "`"
    s
    return (fst:rst)

tk_func = tk_var

tk_class :: Parser String    -- Int, Int_0   // I, II, int, _Int
tk_class = do
    fst <- char 'I'
    snd <- satisfy isUpper
    rst <- many $ (digit <|> letter <|> char '_' <?> "interface identifier")
    --guard $ not $ null $ filter (\c -> isLower c) rst
    when (all isUpper rst) $ unexpected "uppercase identifier"
    s
    return (fst:snd:rst)

tk_data :: Parser String    -- Int, Int_0   // I, II, int, _Int
tk_data = do
    fst <- satisfy isUpper
    rst <- many $ (digit <|> letter <|> char '_' <?> "data identifier")
    --guard $ not $ null $ filter (\c -> isLower c) rst
    --when (fst=='I' && (length rst >= 1) && isUpper (rst!!0)) $ unexpected "uppercase identifier"
    --when (length rst >= 1 && all isUpper rst)                $ unexpected "uppercase identifier"
    s
    return (fst:rst)

tk_data_hier :: Parser ID_Data_Hier
tk_data_hier = do
  v <- (:) <$> tk_data <*> many (try $ tk_sym "." *> tk_data)
  return v

tk_key :: String -> Parser String
tk_key k = do
    key  <- string k
    void <- notFollowedBy (letter <|> char '_' <|> digit)
    guard $ elem key keywords
    s
    return key
