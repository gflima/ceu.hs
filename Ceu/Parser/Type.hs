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
import Ceu.Grammar.Type               (Type(..), TypeC, FuncType(..))

singleton x = [x]

type_0 :: Bool -> Parser Type
type_0 ref = do
    void <- tk_sym "("
    void <- tk_sym ")"
    return $ TUnit ref

f tp = case tp of
  TUnit _    -> []
  TTuple _ l -> l
  _          -> [tp]

type_D :: Bool -> Parser Type
type_D ref = do
    hier <- tk_data_hier
    ofs  <- option (TUnit False) $ try (tk_key "of" *> pType)
    return $ TData ref hier (f ofs) (TUnit False)

type_N :: Bool -> Parser Type
type_N ref = do
    tps <- list2 pType
    return $ TTuple ref tps

type_F :: Bool -> Parser Type
type_F ref = do
    void <- tk_sym "("
    inp  <- pType
    void <- tk_sym "->"
    out  <- pType
    void <- tk_sym ")"
    return $ TFunc ref FuncUnknown inp out

type_V :: Bool -> Parser Type
type_V ref = do
    var <- tk_var
    return $ TAny ref var

type_parens :: Parser Type
type_parens = do
  void <- tk_sym "("
  tp   <- pType
  void <- tk_sym ")"
  return tp

pType' :: Parser Type
pType' = do
  ref <- option False $ do
                          void <- try $ tk_key "ref"
                          return True
  tp  <- type_D ref <|> try (type_V ref) <|> try (type_0 ref) <|>
          try (type_N ref) <|> try (type_F ref) <|> type_parens
  return tp

pType :: Parser Type
pType = do
  tp <- pType' <?> "type"
  return tp

pTypeContext :: Parser TypeC
pTypeContext = do
  tp   <- pType
  ctxs <- option [] $ try pContext
  return $ (tp, foldr Cs.insert cz ctxs)

pContext :: Parser [Cs.Pair]
pContext = do
  void <- try $ tk_key "where"
  ret  <- try (list1 pIs) <|> (singleton <$> pIs)
  return ret

pIs :: Parser Cs.Pair
pIs = do
  var  <- tk_var
  void <- tk_key "is"
  cls  <- tk_class
  return (var,cls)
