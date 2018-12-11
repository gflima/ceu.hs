module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)        -- filename, line, column

class Ann a where
  getSource :: a -> Maybe Source
  getN      :: a -> Int

class INode a where
  toSource :: a -> Maybe Source
  toWord   :: a -> String
  toError  :: a -> String -> String
  toN      :: a -> Int
  toError stmt msg = src ++ (toWord stmt) ++ ": " ++ msg where
    src = case toSource stmt of
      Nothing        -> ""
      Just (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

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
