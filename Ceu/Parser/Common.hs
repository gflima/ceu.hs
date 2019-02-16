module Ceu.Parser.Common where

import Text.Parsec.Prim         (try)
import Text.Parsec.Pos          (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.Parsec.String       (Parser)
import Text.Parsec.Combinator   (many1, optional)

import Ceu.Grammar.Globals      (Source)

import Ceu.Parser.Token

pos2src :: SourcePos -> Source
pos2src pos = (sourceName pos, sourceLine pos, sourceColumn pos)

list :: Parser a -> Parser [a]
list p = do
    void <- tk_sym "("
    v    <- p
    vs   <- many1 $ try (tk_sym "," *> p)
    void <- optional $ tk_sym ","
    void <- tk_sym ")"
    return (v:vs)


