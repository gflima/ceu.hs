module Ceu.Parser.Type where

import Text.Parsec.Prim         ((<|>), (<?>), try)
import Text.Parsec.String       (Parser)
import Text.Parsec.Prim         (many)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_sym, tk_var, tk_type)

import Ceu.Grammar.Globals      (ID_Type)
import Ceu.Grammar.Type         (Type(..))

tk_types :: Parser [ID_Type]
tk_types = do
  v <- (:) <$> tk_type <*> many (try $ tk_sym "." *> tk_type)
  return v

type_0 :: Parser Type
type_0 = do
    void <- tk_sym "("
    void <- tk_sym ")"
    return Type0

type_1 :: Parser Type
type_1 = do
    tp <- tk_types
    return $ Type1 tp

type_N :: Parser Type
type_N = do
    tps <- list pType
    return $ TypeN tps

type_F :: Parser Type
type_F = do
    void <- tk_sym "("
    inp   <- pType
    void <- tk_sym "->"
    out   <- pType
    void <- tk_sym ")"
    return $ TypeF inp out

type_V :: Parser Type
type_V = do
    var <- tk_var
    return $ TypeV var

type_parens :: Parser Type
type_parens = do
  void <- tk_sym "("
  tp   <- pType
  void <- tk_sym ")"
  return tp

pType :: Parser Type
pType = type_1 <|> try type_V <|> try type_0 <|> try type_N <|> try type_F
        <|> type_parens <?> "type"
