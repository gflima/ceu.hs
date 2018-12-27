module Ceu.Parser.Exp where

import Text.Parsec.Prim         ((<|>), getPosition, try, many)
import Text.Parsec.Pos          (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String       (Parser)
import Text.Parsec.Char         (char, anyChar)
import Text.Parsec.Combinator   (many1, chainl1, option, notFollowedBy)

import Ceu.Parser.Token         (tk_num, tk_var, tk_str, s)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp          (Exp(..), RawAt(..))

pos2src :: SourcePos -> Source
pos2src pos = (sourceName pos, sourceLine pos, sourceColumn pos)

-------------------------------------------------------------------------------

tk_raw :: Parser [RawAt Source]
tk_raw = do
    void <- char '{'
    vs   <- many $ (try tk_raw <|> try rawe <|> try raws)
    void <- char '}'
    s
    return $ concat $ [[RawAtS "{"]] ++ vs ++ [[RawAtS "}"]]
    where
        rawe :: Parser [RawAt Source]
        rawe = do
            e <- char '@' *> ((try (char '(') *> (expr <* char ')')) <|> expr)
            return [RawAtE e]

        raws :: Parser [RawAt Source]
        raws = do
            str <- raws'
            return [RawAtS str]
        raws' = do
            notFollowedBy (char '}' <|> char '@')
            c  <- anyChar
            cs <- option [] raws'
            return (c:cs)

-------------------------------------------------------------------------------

expr_raw :: Parser (Exp Source)
expr_raw = do
    pos <- pos2src <$> getPosition
    vs  <- tk_raw
    return $ RawE pos vs

expr_const :: Parser (Exp Source)
expr_const = do
    pos <- pos2src <$> getPosition
    num <- tk_num
    return $ Const pos num

expr_unit :: Parser (Exp Source)
expr_unit = do
    pos <- pos2src <$> getPosition
    void <- tk_str "("
    void <- tk_str ")"
    return $ Unit pos

expr_tuple :: Parser (Exp Source)
expr_tuple = do
    pos  <- pos2src <$> getPosition
    void <- tk_str "("
    exp1 <- expr
    exps <- many1 expr
    void <- tk_str ")"
    return $ Tuple pos (exp1:exps)

expr_read :: Parser (Exp Source)
expr_read = do
    pos <- pos2src <$> getPosition
    str <- tk_var
    return $ Read pos str

expr_umn :: Parser (Exp Source)
expr_umn = do
    pos  <- pos2src <$> getPosition
    void <- tk_str "-"
    exp  <- expr
    return $ Call pos "(-1)" exp

expr_parens :: Parser (Exp Source)
expr_parens = do
    void <- tk_str "("
    exp  <- expr
    void <- tk_str ")"
    return exp

expr_prim :: Parser (Exp Source)
expr_prim = (try expr_raw <|> try expr_const <|> try expr_unit <|> try expr_tuple <|> try expr_read <|> try expr_umn <|> try expr_parens)

-------------------------------------------------------------------------------

expr_add_sub :: Parser (Exp Source)
expr_add_sub = chainl1 expr_mul_div op where
    op = do
        pos  <- pos2src <$> getPosition
        void <- tk_str "+"
        return (\a b -> Call pos "(+)" (Tuple pos [a,b]))
     <|> do
        pos  <- pos2src <$> getPosition
        void <- tk_str "-"
        return (\a b -> Call pos "(-)" (Tuple pos [a,b]))

expr_mul_div :: Parser (Exp Source)
expr_mul_div = chainl1 expr_equ op where
    op = do
        pos  <- pos2src <$> getPosition
        void <- tk_str "*"
        return (\a b -> Call pos "(*)" (Tuple pos [a,b]))
     <|> do
        pos  <- pos2src <$> getPosition
        void <- tk_str "/"
        return (\a b -> Call pos "(/)" (Tuple pos [a,b]))

expr_equ :: Parser (Exp Source)
expr_equ = chainl1 expr_prim op where
    op = do
        pos  <- pos2src <$> getPosition
        void <- tk_str "=="
        return (\a b -> Call pos "(==)" (Tuple pos [a,b]))

-------------------------------------------------------------------------------

expr :: Parser (Exp Source)
expr = do
    e <- expr_add_sub
    return e
