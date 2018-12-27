module Ceu.Parser.Type where

import Text.Parsec.Prim         ((<|>), try)
import Text.Parsec.String       (Parser)
import Text.Parsec.Combinator   (many1)

import Ceu.Parser.Token         (tk_str, tk_type)

import Ceu.Grammar.Type         (Type(..))

{-
--import Text.Parsec.Prim         ((<|>), getPosition, try, many)
import Text.Parsec.Pos          (SourcePos, sourceName, sourceLine, sourceColumn)
--import Text.Parsec.String       (Parser)
import Text.Parsec.Char         (char, anyChar)
--import Text.Parsec.Combinator   (chainl1, option, optionMaybe, notFollowedBy)

--import Ceu.Parser.Token         (tk_num, tk_var, tk_str, s)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp          (Exp(..), RawAt(..))
-}

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
    void <- tk_str "("
    tp1  <- type_
    tps  <- many1 type_
    void <- tk_str ")"
    return $ TypeN (tp1:tps)

type_ :: Parser Type
type_ = try type_0 <|> try type_1 <|> try type_N
