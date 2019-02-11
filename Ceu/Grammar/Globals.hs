module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column

type ID_Class = String   -- type identifier/constructor
type ID_Type  = String   -- type identifier/constructor
type ID_Var   = String   -- variable identifier
