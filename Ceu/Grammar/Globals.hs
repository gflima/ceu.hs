module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column

type ID_Var       = String
type ID_Class     = String
type ID_Data      = String
type ID_Data_Hier = [ID_Data]
