module Ceu.Parser.Type where

import qualified Data.Set as Set
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

type_0 :: Parser Type
type_0 = do
    void <- tk_sym "("
    void <- tk_sym ")"
    return TUnit

f tp = case tp of
  TUnit    -> []
  TTuple l -> l
  _        -> [tp]

type_D :: Parser Type
type_D = do
    ref  <- option False $ do
                            void <- try $ tk_key "ref"
                            return True
    hier <- tk_data_hier
    ofs  <- option TUnit $ try (tk_key "of" *> pType)
    return $ TData ref hier (f ofs) TUnit

type_N :: Parser Type
type_N = do
    tps <- list2 pType
    return $ TTuple tps

type_F :: Parser Type
type_F = do
    void <- tk_sym "("
    inp  <- pType
    void <- tk_sym "->"
    out  <- pType
    void <- tk_sym ")"
    return $ TFunc FuncUnknown inp out

type_V :: Parser Type
type_V = do
    ref <- option False $ do
                            void <- try $ tk_key "ref"
                            return True
    var <- tk_var
    return $ TVar ref var

type_parens :: Parser Type
type_parens = do
  void <- tk_sym "("
  tp   <- pType
  void <- tk_sym ")"
  return tp

pType :: Parser Type
pType = do
  tp  <- type_D <|> try type_V <|> try type_0 <|>
          try type_N <|> try type_F <|> type_parens <?> "type"
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
