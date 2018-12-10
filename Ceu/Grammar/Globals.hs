module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)        -- filename, line, column

class Ann a where
  toSourceString :: a -> String
  toN            :: a -> Int

class INode a where
  toSource :: a -> String
  toWord   :: a -> String
  toError  :: a -> String -> String
  toError stmt msg = (toSource stmt) ++ (toWord stmt) ++ ": " ++ msg where

errs_nodes_msg_map :: (INode a) => [a] -> String -> Errors
errs_nodes_msg_map node msg = map (\s -> (toWord s) ++ ": " ++ msg) node

-- Primitive types.
type ID_Var = String            -- variable identifier
type ID_Evt = String            -- event identifier
type ID_Ext = String            -- external event identifier
type ID_Int = String            -- internal event identifier
type Val    = Int               -- value

-- Special events:
-- "BOOT"
-- "FOREVER"
