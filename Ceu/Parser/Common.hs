module Ceu.Parser.Common where

import Data.Bool                (bool)

import Text.Parsec.Prim         (try,many)
import Text.Parsec.Pos          (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String       (Parser)
import Text.Parsec.Combinator   (many1, optional)

import Ceu.Grammar.Globals      (Source)

import Ceu.Parser.Token

pos2src :: SourcePos -> Source
pos2src pos = (sourceName pos, sourceLine pos, sourceColumn pos)

list :: Bool -> Parser a -> Parser [a]
list one p = do
    void <- tk_sym "("
    v    <- p
    vs   <- (bool many1 many one) $ try (tk_sym "," *> p)
    void <- optional $ tk_sym ","
    void <- tk_sym ")"
    return (v:vs)

list1 = list True
list2 = list False
