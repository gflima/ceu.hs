module Ceu.Parser.Type where

import Control.Exception        (assert)

import Text.Parsec.Prim         ((<|>), (<?>), try)
import Text.Parsec.Prim         ((<|>), (<?>), try)
import Text.Parsec.String       (Parser)
import Text.Parsec.Prim         (many)
import Text.Parsec.Combinator   (optionMaybe)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_sym, tk_key, tk_class, tk_var, tk_data_hier)

import Ceu.Grammar.Globals      (ID_Var, ID_Class)
import Ceu.Grammar.Type         (Type(..))

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
    return $ TypeV var []

type_parens :: Parser Type
type_parens = do
  void <- tk_sym "("
  tp   <- pType
  void <- tk_sym ")"
  return tp

pType :: Parser Type
pType = type_1 <|> try type_V <|> try type_0 <|> try type_N <|> try type_F
        <|> type_parens <?> "type"

pTypeIfc :: Parser Type
pTypeIfc = do
  tp  <- pType
  ifc <- optionMaybe ((,) <$> (try (tk_key "where") *> ((singleton <$> tk_var) <|> list tk_var)) <*> (tk_key "implements" *> ((singleton <$> tk_class) <|> list tk_class)))
  return $ implements tp ifc

implements :: Type -> Maybe ([ID_Var],[ID_Class]) -> Type
implements tp Nothing = tp
implements tp (Just (l1,l2)) = aux tp $ assert (length l1 == length l2) (zip l1 l2)
  where
    aux :: Type -> [(ID_Var,ID_Class)] -> Type
    aux tp l = foldr f tp l

    f :: (ID_Var,ID_Class) -> Type -> Type
    f (var,cls) (TypeV var' []) | var==var' = TypeV var [cls]
    f (var,cls) (TypeF inp out) = TypeF (f (var,cls) inp) (f (var,cls) out)
    f (var,cls) (TypeN ts)      = TypeN $ map (f (var,cls)) ts
    f _         tp              = tp
