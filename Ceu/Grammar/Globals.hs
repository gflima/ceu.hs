module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)        -- filename, line, column

-- Primitive types.
type ID_Var = String            -- variable identifier
type ID_Evt = String            -- event identifier
type ID_Ext = String            -- external event identifier
type ID_Int = String            -- internal event identifier
type Val    = Int               -- value

-- Special events:
-- "BOOT"
-- "FOREVER"
