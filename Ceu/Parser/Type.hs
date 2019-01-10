module Ceu.Parser.Type where

import Text.Parsec.Prim         ((<|>), try)
import Text.Parsec.String       (Parser)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_str, tk_type, tk_var)

import Ceu.Grammar.Type         (Type(..))

type_0 :: Parser Type
type_0 = do
    void <- tk_str "("
    void <- tk_str ")"
    return Type0

type_1 :: Parser Type
type_1 = do
    tp <- tk_type
    return $ Type1 [tp]

type_N :: Parser Type
type_N = do
    tps <- list pType
    return $ TypeN tps

type_F :: Parser Type
type_F = do
    void <- tk_str "("
    inp   <- pType
    void <- tk_str "->"
    out   <- pType
    void <- tk_str ")"
    return $ TypeF inp out

type_V :: Parser Type
type_V = do
    var <- tk_var
    return $ TypeV var

pType :: Parser Type
pType = try type_0 <|> try type_1 <|> try type_N <|> try type_F <|> try type_V
