module Ceu.Parser.Stmt where

import Debug.Trace
import Control.Monad             (guard)
import Control.Applicative       (many)

import Text.Parsec.Prim          ((<|>), try, getPosition)
import Text.Parsec.String        (Parser)
import Text.Parsec.Combinator    (many1, chainl, chainr1, option, optionMaybe)

import Ceu.Parser.Token          (tk_key, tk_ext, tk_var, tk_type, tk_str)
import Ceu.Parser.Exp            (toSource, expr)

import Ceu.Grammar.Globals       (Source)
import Ceu.Grammar.Exp           (Exp(..))
import Ceu.Grammar.Full.Grammar  (Stmt(..))

-------------------------------------------------------------------------------

attr_exp :: String -> Parser (Stmt Source)
attr_exp var = do
    pos  <- getPosition
    void <- tk_str "<-"
    exp  <- expr
    return $ Write (toSource pos) var exp

attr_awaitext :: String -> Parser (Stmt Source)
attr_awaitext var = do
    void <- tk_str "<-"
    p    <- stmt_awaitext (Just var)
    return p

-------------------------------------------------------------------------------

stmt_nop :: Parser (Stmt Source)
stmt_nop = do
    pos  <- getPosition
    return $ Nop (toSource pos)

stmt_escape :: Parser (Stmt Source)
stmt_escape = do
    pos  <- getPosition
    void <- tk_key "escape"
    e    <- expr
    return $ Escape (toSource pos) Nothing (Just e)

stmt_var :: Parser (Stmt Source)
stmt_var = do
    pos  <- getPosition
    void <- tk_key "var"
    tp   <- tk_type
    var  <- tk_var
    guard $ tp == "int"         -- TODO
    p    <- option (Nop $ toSource pos) (try (attr_exp var) <|> try (attr_awaitext var))
    return $ Seq (toSource pos) (Var (toSource pos) var Nothing) p

stmt_write :: Parser (Stmt Source)
stmt_write = do
    pos  <- getPosition
    var  <- tk_var
    void <- tk_str "<-"
    exp  <- expr
    return $ Write (toSource pos) var exp

-------------------------------------------------------------------------------

stmt_emitext :: Parser (Stmt Source)
stmt_emitext = do
    pos  <- getPosition
    void <- tk_key "emit"
    ext  <- tk_ext
    exp  <- optionMaybe (tk_str "->" *> expr)
    return $ EmitExt (toSource pos) ext exp

stmt_awaitext :: (Maybe String) -> Parser (Stmt Source)
stmt_awaitext var = do
    pos  <- getPosition
    void <- tk_key "await"
    ext  <- tk_ext
    return $ AwaitExt (toSource pos) ext var

-------------------------------------------------------------------------------

stmt_do :: Parser (Stmt Source)
stmt_do = do
    pos  <- getPosition
    void <- tk_key "do"
    p    <- stmt <|> stmt_nop
    void <- tk_key "end"
    return $ Scope (toSource pos) p

stmt_if :: Parser (Stmt Source)
stmt_if = do
    pos1 <- getPosition
    void <- tk_key "if"
    cnd  <- expr
    void <- tk_key "then"
    s1   <- stmt
    ss   <- many $ (try $ (,,) <$> getPosition <*> (tk_key "else/if" *> expr) <*> (tk_key "then" *> stmt))
    pos2 <- getPosition
    s2   <- option (Nop $ toSource pos2) (try $ tk_key "else" *> stmt)
    void <- tk_key "end"
    return $ foldr (\(p,c,s) acc -> If (toSource p) c s acc) s2 ([(pos1,cnd,s1)] ++ ss)

-------------------------------------------------------------------------------

stmt_par :: Parser (Stmt Source)
stmt_par = do
    pos1 <- getPosition
    void <- tk_key "par"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> getPosition <*> (tk_key "with" *> stmt))
    pos2 <- getPosition
    void <- tk_key "end"
    return $ foldr (\(p,s) acc -> Par (toSource p) s acc)
                   (AwaitFor $ toSource pos2) ([(pos1,s1)]++ss)

stmt_parand :: Parser (Stmt Source)
stmt_parand = do
    pos1 <- getPosition
    void <- tk_key "par/and"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> getPosition <*> (tk_key "with" *> stmt))
    pos2 <- getPosition
    void <- tk_key "end"
    return $ foldr (\(p,s) acc -> And (toSource p) s acc)
                   (Nop $ toSource pos2) ([(pos1,s1)]++ss)

stmt_paror :: Parser (Stmt Source)
stmt_paror = do
    pos1 <- getPosition
    void <- tk_key "par/or"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> getPosition <*> (tk_key "with" *> stmt))
    pos2 <- getPosition
    void <- tk_key "end"
    return $ foldr (\(p,s) acc -> Or (toSource p) s acc)
                   (AwaitFor $ toSource pos2) ([(pos1,s1)]++ss)

-------------------------------------------------------------------------------

stmt1 :: Parser (Stmt Source)
stmt1 = do
    s <- try stmt_escape <|> try stmt_var <|> try stmt_write <|>
         try (stmt_awaitext Nothing) <|> try stmt_emitext <|>
         try stmt_do <|> stmt_if <|>
         try stmt_par <|> try stmt_parand <|> try stmt_paror
    return s

stmt_seq :: Source -> Parser (Stmt Source)
stmt_seq src = option (Nop src) (chainr1 stmt1 (do return (\a b->Seq src a b)))

stmt :: Parser (Stmt Source)
stmt = do
    pos <- getPosition
    s   <- stmt_seq (toSource pos)
    return s

