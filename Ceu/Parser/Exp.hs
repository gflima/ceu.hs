module Ceu.Parser.Exp where

import Text.Parsec.Prim         ((<|>), getPosition, try, many)
import Text.Parsec.Pos          (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String       (Parser)
import Text.Parsec.Char         (char, anyChar)
import Text.Parsec.Combinator   (many1, chainl1, option, notFollowedBy)

import Ceu.Parser.Token         (tk_num, tk_var, tk_func, tk_str, tk_op, s)

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (annz, source)
import Ceu.Grammar.Exp          (Exp(..), RawAt(..))

pos2src :: SourcePos -> Source
pos2src pos = (sourceName pos, sourceLine pos, sourceColumn pos)

-------------------------------------------------------------------------------

tk_raw :: Parser [RawAt]
tk_raw = do
    void <- char '{'
    vs   <- many $ (try tk_raw <|> try rawe <|> try raws)
    void <- char '}'
    s
    return $ concat $ [[RawAtS "{"]] ++ vs ++ [[RawAtS "}"]]
    where
        rawe :: Parser [RawAt]
        rawe = do
            e <- char '`' *> (expr <* char '`')
            return [RawAtE e]

        raws :: Parser [RawAt]
        raws = do
            str <- raws'
            return [RawAtS str]
        raws' = do
            notFollowedBy (char '}' <|> char '`')
            c  <- anyChar
            cs <- option [] raws'
            return (c:cs)

-------------------------------------------------------------------------------

expr_raw :: Parser Exp
expr_raw = do
    pos <- pos2src <$> getPosition
    vs  <- tk_raw
    return $ RawE annz{source=pos} vs

expr_const :: Parser Exp
expr_const = do
    pos <- pos2src <$> getPosition
    num <- tk_num
    return $ Const annz{source=pos} num

expr_read :: Parser Exp
expr_read = do
    pos <- pos2src <$> getPosition
    str <- tk_var
    return $ Read annz{source=pos} str

expr_unit :: Parser Exp
expr_unit = do
    pos <- pos2src <$> getPosition
    void <- tk_str "("
    void <- tk_str ")"
    return $ Unit annz{source=pos}

expr_parens :: Parser Exp
expr_parens = do
    void <- tk_str "("
    exp  <- expr
    void <- tk_str ")"
    return exp

expr_tuple :: Parser Exp
expr_tuple = do
    pos  <- pos2src <$> getPosition
    void <- tk_str "("
    exp1 <- expr
    exps <- many1 expr
    void <- tk_str ")"
    return $ Tuple annz{source=pos} (exp1:exps)

expr_call_pre :: Parser Exp
expr_call_pre = do
    pos  <- pos2src <$> getPosition
    f    <- try tk_op <|> try tk_func
    exp  <- expr
    return $ Call annz{source=pos} (if f == "(-)" then "negate" else f) exp
                        -- TODO: unary minus exception

expr_prim :: Parser Exp
expr_prim = try expr_raw        <|>
            try expr_const      <|>
            try expr_read       <|>
            try expr_unit       <|>
            try expr_parens     <|>
            try expr_tuple      <|>
            try expr_call_pre

-------------------------------------------------------------------------------

expr_call_pos :: Parser Exp
expr_call_pos = do
    pos <- pos2src <$> getPosition
    e1  <- expr_call_inf
    ops <- many (try tk_op <|> try (char '`' *> (tk_func <* char '`')))
    return $ foldl (\e op -> Call annz{source=pos} op e) e1 ops

expr_call_inf :: Parser Exp
expr_call_inf = chainl1 expr_prim f where
    f = do
        pos <- pos2src <$> getPosition
        op  <- try tk_op <|> try (char '`' *> (tk_func <* char '`'))
        return (\a b -> Call annz{source=pos} op (Tuple annz{source=pos} [a,b]))

-------------------------------------------------------------------------------

expr :: Parser Exp
expr = do
    e <- expr_call_pos
    return e
