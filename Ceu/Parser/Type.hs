module Ceu.Parser.Type where

import Text.Parsec.Prim         ((<|>), try)
import Text.Parsec.String       (Parser)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_str, tk_type)

import Ceu.Grammar.Type         (Type(..))

type_0 :: Parser Type
type_0 = do
    void <- tk_str "("
    void <- tk_str ")"
    return Type0

type_1 :: Parser Type
type_1 = do
    tp <- tk_type
    return $ Type1 tp

type_N :: Parser Type
type_N = do
    tps <- list type_
    return $ TypeN tps

type_ :: Parser Type
type_ = try type_0 <|> try type_1 <|> try type_N
