module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column

data Loc = LAny
         | LVar ID_Var
         | LUnit
         | LNumber Int
         | LCons ID_Type Loc
         | LRead ID_Var
         | LTuple [Loc]
  deriving (Eq, Show)

type ID_Class = String   -- type identifier/constructor
type ID_Type  = String   -- type identifier/constructor
type ID_Var   = String   -- variable identifier

newtype DataCons = DataCons (Either ID_Var (ID_Type,[DataCons]))
    deriving (Eq, Show)
