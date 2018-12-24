module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column
type Trails = (Int, Int)            -- trail_0, trail_n

class Ann a where
  getSource :: a -> Maybe Source
  getN      :: a -> Int
  getTrails :: a -> Trails

class INode a where
  toWord   :: a -> String
  toError  :: a -> String -> String
  toError stmt msg = src ++ (toWord stmt) ++ ": " ++ msg where
    src = case toSource stmt of
      Nothing        -> ""
      Just (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

  toTrails0 :: a -> Int
  toTrails0 = fst . toTrails
  toTrailsN :: a -> Int
  toTrailsN = snd . toTrails

  toSource :: a -> Maybe Source
  toN      :: a -> Int
  toTrails :: a -> (Int,Int)

errs_nodes_msg_map :: (INode a) => [a] -> String -> Errors
errs_nodes_msg_map node msg = map (\s -> (toWord s) ++ ": " ++ msg) node

-- Primitive types.
type ID     = String            -- identifier
type ID_Var = String            -- variable identifier
type ID_Ext = String            -- external event identifier
type ID_Inp = String            -- external event identifier
type ID_Out = String            -- external event identifier
type ID_Evt = String            -- event identifier
type Val    = Int               -- value

-- Special events:
-- "BOOT"
