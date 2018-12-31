module Ceu.Parser.Stmt where

import Debug.Trace
import Control.Monad             (guard)
import Control.Applicative       (many)

import Text.Parsec.Prim          ((<|>), try, getPosition)
import Text.Parsec.String        (Parser)
import Text.Parsec.Combinator    (many1, chainl, chainr1, option, optionMaybe)

import Ceu.Parser.Token
import Ceu.Parser.Type           (type_)
import Ceu.Parser.Exp            (pos2src, expr, tk_raw)

import Ceu.Grammar.Globals       (Source)
import Ceu.Grammar.Type          (Type(..))
import Ceu.Grammar.Ann           (annz, source)
import Ceu.Grammar.Exp           (Exp(..))
import Ceu.Grammar.Full.Grammar  (Stmt(..))

-------------------------------------------------------------------------------

attr_exp :: String -> Parser a -> Parser Stmt
attr_exp var op = do
    pos  <- pos2src <$> getPosition
    void <- op
    exp  <- expr
    return $ Write annz{source=pos} var exp

attr_awaitext :: String -> Parser a -> Parser Stmt
attr_awaitext var op = do
    void <- op
    s    <- stmt_awaitext (Just var)
    return s

attr_awaitevt :: String -> Parser a -> Parser Stmt
attr_awaitevt var op = do
    void <- op
    s    <- stmt_awaitevt (Just var)
    return s

-------------------------------------------------------------------------------

stmt_nop :: Parser Stmt
stmt_nop = do
    pos  <- pos2src <$> getPosition
    return $ Nop annz{source=pos}

stmt_raw :: Parser Stmt
stmt_raw = do
    pos <- pos2src <$> getPosition
    vs  <- tk_raw
    return $ RawS annz{source=pos} vs

stmt_escape :: Parser Stmt
stmt_escape = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "escape"
    e    <- optionMaybe (try expr)
    return $ Escape annz{source=pos} Nothing e

stmt_break :: Parser Stmt
stmt_break = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "break"
    return $ Break annz{source=pos}

stmt_var :: Parser Stmt
stmt_var = do
    pos  <- pos2src <$> getPosition
    void <- (tk_key "val" <|> tk_key "mut")
    var  <- tk_var
    void <- tk_str "::"
    tp   <- type_
    s    <- option (Nop $ annz{source=pos}) (try (attr_exp var (tk_str ":")) <|> try (attr_awaitext var (tk_str ":")) <|> try (attr_awaitevt var (tk_str ":")))
    return $ Seq annz{source=pos} (Var annz{source=pos} var tp Nothing) s

stmt_evt :: Parser Stmt
stmt_evt = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "event"
    evt  <- tk_evt
    void <- tk_str "::"
    tp   <- tk_type
    guard $ tp == "Int"         -- TODO
    return $ Evt annz{source=pos} evt True

stmt_input :: Parser Stmt
stmt_input = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "input"
    ext  <- tk_ext
    void <- tk_str "::"
    tp   <- tk_type
    guard $ tp == "Int"         -- TODO
    return $ Inp annz{source=pos} ext True

stmt_output :: Parser Stmt
stmt_output = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "output"
    ext  <- tk_ext
    void <- tk_str "::"
    tp   <- tk_type
    guard $ tp == "Int"         -- TODO
    return $ Out annz{source=pos} ext True

stmt_attr :: Parser Stmt
stmt_attr = do
    --pos  <- pos2src <$> getPosition
    var  <- tk_var
    s    <- try (attr_exp var (tk_str "<:")) <|> try (attr_awaitext var (tk_str "<:")) <|> try (attr_awaitevt var (tk_str "<:"))
    return $ s

-------------------------------------------------------------------------------

stmt_emitext :: Parser Stmt
stmt_emitext = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "emit"
    ext  <- tk_ext
    exp  <- optionMaybe (tk_str "->" *> expr)
    return $ EmitExt annz{source=pos} ext exp

stmt_awaitext :: (Maybe String) -> Parser Stmt
stmt_awaitext var = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "await"
    ext  <- tk_ext
    return $ AwaitInp annz{source=pos} ext var

stmt_halt :: Parser Stmt
stmt_halt = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "await"
    void <- tk_key "FOREVER"
    return $ Halt annz{source=pos}

stmt_emitevt :: Parser Stmt
stmt_emitevt = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "emit"
    evt  <- tk_evt
    exp  <- optionMaybe (tk_str "->" *> expr)
    return $ EmitEvt annz{source=pos} evt exp

stmt_awaitevt :: (Maybe String) -> Parser Stmt
stmt_awaitevt var = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "await"
    evt  <- tk_evt
    return $ AwaitEvt annz{source=pos} evt var

-------------------------------------------------------------------------------

stmt_do :: Parser Stmt
stmt_do = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "do"
    s    <- stmt
    void <- tk_key "end"
    return $ Scope annz{source=pos} s

stmt_if :: Parser Stmt
stmt_if = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "if"
    cnd  <- expr
    void <- tk_key "then"
    s1   <- stmt
    ss   <- many $ (try $ (,,) <$> pos2src <$> getPosition <*> (tk_key "else/if" *> expr) <*> (tk_key "then" *> stmt))
    pos2 <- pos2src <$> getPosition
    s2   <- option (Nop annz{source=pos2}) (try $ tk_key "else" *> stmt)
    void <- tk_key "end"
    return $ foldr (\(p,c,s) acc -> If annz{source=p} c s acc) s2 ([(pos1,cnd,s1)] ++ ss)

stmt_loop :: Parser Stmt
stmt_loop = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "loop"
    void <- tk_key "do"
    s    <- stmt
    --pos2 <- pos2src <$> getPosition
    void <- tk_key "end"
    return $ Loop annz{source=pos1} s

stmt_trap :: Parser Stmt
stmt_trap = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "trap"
    void <- tk_key "do"
    s    <- stmt
    void <- tk_key "end"
    return $ Trap annz{source=pos} Nothing s

-------------------------------------------------------------------------------

stmt_par :: Parser Stmt
stmt_par = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "par"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> pos2src <$> getPosition <*> (tk_key "with" *> stmt))
    --pos2 <- pos2src <$> getPosition
    void <- tk_key "end"
    return $ snd $ foldr1 (\(p,s) acc -> (p, Par annz{source=p} s (snd acc)))
                          ([(pos1,s1)]++ss)

stmt_parand :: Parser Stmt
stmt_parand = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "par/and"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> pos2src <$> getPosition <*> (tk_key "with" *> stmt))
    --pos2 <- pos2src <$> getPosition
    void <- tk_key "end"
    return $ snd $ foldr1 (\(p,s) acc -> (p, And annz{source=p} s (snd acc)))
                          ([(pos1,s1)]++ss)

stmt_paror :: Parser Stmt
stmt_paror = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "par/or"
    void <- tk_key "do"
    s1   <- stmt
    ss   <- many1 $ (try $ (,) <$> pos2src <$> getPosition <*> (tk_key "with" *> stmt))
    --pos2 <- pos2src <$> getPosition
    void <- tk_key "end"
    return $ snd $ foldr1 (\(p,s) acc -> (p, Or annz{source=p} s (snd acc)))
                          ([(pos1,s1)]++ss)

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
    s <- try stmt_raw <|> try stmt_escape <|> try stmt_break <|>
         try stmt_var <|> try stmt_input <|> try stmt_output <|> try stmt_evt <|>
         try stmt_attr <|>
         try (stmt_awaitext Nothing) <|> try stmt_halt <|> try (stmt_awaitevt Nothing) <|>
         try stmt_emitext <|> try stmt_emitevt <|>
         try stmt_do <|> try stmt_if <|> try stmt_loop <|> try stmt_trap <|>
         try stmt_par <|> try stmt_parand <|> try stmt_paror
    return s

stmt_seq :: Source -> Parser Stmt
stmt_seq src = option (Nop annz{source=src}) (chainr1 stmt1 (do return (\a b->Seq annz{source=src} a b)))

stmt :: Parser Stmt
stmt = do
    pos <- pos2src <$> getPosition
    s   <- stmt_seq pos
    return s

