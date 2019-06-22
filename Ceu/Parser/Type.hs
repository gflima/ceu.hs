module Ceu.Parser.Type where

import Control.Exception        (assert)

import Text.Parsec.Prim         ((<|>), (<?>), try)
import Text.Parsec.Prim         ((<|>), (<?>), try)
import Text.Parsec.String       (Parser)
import Text.Parsec.Prim         (many)
import Text.Parsec.Combinator   (option)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_sym, tk_key, tk_class, tk_var, tk_data_hier)

import Ceu.Grammar.Globals            (ID_Var, ID_Class)
import Ceu.Grammar.Constraints as Cs  (Pair, insert, cz)
import Ceu.Grammar.Type               (Type(..), TypeC)

singleton x = [x]

type_0 :: Parser Type
type_0 = do
    void <- tk_sym "("
    void <- tk_sym ")"
    return Type0

type_1 :: Parser Type
type_1 = do
    tp <- tk_data_hier
    return $ TypeD tp

type_N :: Parser Type
type_N = do
    tps <- list2 pType
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

pTypeContext :: Parser TypeC
pTypeContext = do
  tp   <- pType
  ctxs <- option [] pContext
  return $ (tp, foldr Cs.insert cz ctxs)

pContext :: Parser [Cs.Pair]
pContext = do
  void <- try $ tk_key "where"
  ret  <- (singleton <$> pIs) <|> list1 pIs
  return ret

pIs :: Parser Cs.Pair
pIs = do
  var  <- tk_var
  void <- tk_key "is"
  cls  <- tk_class
  return (var,cls)
