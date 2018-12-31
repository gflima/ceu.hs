module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column
type Trails = (Int, Int)            -- trail_0, trail_n

data Loc = LAny | LVar ID_Var | LTuple [Loc]
    deriving (Eq, Show)

-- Primitive types.
type ID      = String   -- identifier
type ID_Type = String   -- type identifier
type ID_Var  = String   -- variable identifier
type ID_Ext  = String   -- external event identifier
type ID_Inp  = String   -- external event identifier
type ID_Out  = String   -- external event identifier
type ID_Evt  = String   -- event identifier
type ID_Func = String   -- function identifier
type Val     = Int      -- value

-- Special events:
-- "BOOT"
