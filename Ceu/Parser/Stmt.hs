module Ceu.Parser.Stmt where

import Debug.Trace
import Control.Monad                    (guard)
import Control.Applicative              (many)

import Text.Parsec.Prim                 ((<|>), try)
import Text.Parsec.String               (Parser)
import Text.Parsec.String.Combinator    (many1, chainl, chainr1, option, optionMaybe)

import Ceu.Parser.Token                 (tk_key, tk_var, tk_type, tk_str)
import Ceu.Parser.Exp                   (expr)

import Ceu.Grammar.Globals              (Exp(..))
import Ceu.Grammar.Full.Grammar         (Stmt(..))

-------------------------------------------------------------------------------

stmt_nop :: Parser Stmt
stmt_nop = do
    return $ Nop

stmt_escape :: Parser Stmt
stmt_escape = do
    void <- tk_key "escape"
    e    <- expr
    return $ Escape Nothing (Just e)

stmt_do :: Parser Stmt
stmt_do = do
    void <- tk_key "do"
    p    <- stmt <|> stmt_nop
    void <- tk_key "end"
    return $ Scope p

stmt_var :: Parser Stmt
stmt_var = do
    void <- tk_key "var"
    tp   <- tk_type
    var  <- tk_var
    guard $ tp == "int"         -- TODO
    exp  <- optionMaybe $ (tk_str "<-") *> expr
    return $ Var var exp Nothing

stmt_write :: Parser Stmt
stmt_write = do
    var  <- tk_var
    void <- tk_str "<-"
    exp  <- expr
    return $ Write var exp

stmt_if :: Parser Stmt
stmt_if = do
    void <- tk_key "if"
    cnd  <- expr
    void <- tk_key "then"
    s1   <- stmt
    ss   <- many $ (try $ (,) <$> (tk_key "else/if" *> expr) <*> (tk_key "then" *> stmt))
    s2   <- option Nop (try $ tk_key "else" *> stmt)
    void <- tk_key "end"
    return $ foldr (\(c,s) acc -> If c s acc) s2 ([(cnd,s1)] ++ ss)

stmt_par :: Parser Stmt
stmt_par = do
    void <- tk_key "par"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ tk_key "with") *> stmt
    void <- tk_key "end"
    return $ foldr1 (\s acc -> Par s acc) ([s1]++ss)

stmt_parand :: Parser Stmt
stmt_parand = do
    void <- tk_key "par/and"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ tk_key "with") *> stmt
    void <- tk_key "end"
    return $ foldr1 (\s acc -> And s acc) ([s1]++ss)

stmt_paror :: Parser Stmt
stmt_paror = do
    void <- tk_key "par/or"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ tk_key "with") *> stmt
    void <- tk_key "end"
    return $ foldr1 (\s acc -> Or s acc) ([s1]++ss)

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
    s <- try stmt_escape <|> try stmt_do <|> try stmt_var <|> try stmt_write <|>
         try stmt_if <|>
         try stmt_par <|> try stmt_parand <|> try stmt_paror
    return s

stmt_seq :: Parser Stmt
stmt_seq = option Nop (chainr1 stmt1 (do return Seq))

stmt :: Parser Stmt
stmt = do
    s <- stmt_seq
    return s

