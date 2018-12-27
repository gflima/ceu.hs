module Ceu.Grammar.Globals where

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column
type Trails = (Int, Int)            -- trail_0, trail_n

data Type = TypeB | TypeT | Type0 | Type1 ID_Type | TypeN [Type] -- (len >= 2)
    deriving (Eq,Show)

class Ann a where
  getSource :: a -> Source
  getN      :: a -> Int
  getTrails :: a -> Trails

class INode a where
  toWord   :: a -> String
  toError  :: a -> String -> String
  toError stmt msg = src ++ (toWord stmt) ++ ": " ++ msg where
    src = case toSource stmt of
      (_,0, 0)  -> ""
      (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

  toTrails0 :: a -> Int
  toTrails0 = fst . toTrails
  toTrailsN :: a -> Int
  toTrailsN = snd . toTrails

  toSource :: a -> Source
  toN      :: a -> Int
  toTrails :: a -> (Int,Int)

errs_nodes_msg_map :: (INode a) => [a] -> String -> Errors
errs_nodes_msg_map node msg = map (\s -> (toWord s) ++ ": " ++ msg) node

-- Primitive types.
type ID      = String   -- identifier
type ID_Type = String   -- type identifier
type ID_Var  = String   -- variable identifier
type ID_Ext  = String   -- external event identifier
type ID_Inp  = String   -- external event identifier
type ID_Out  = String   -- external event identifier
type ID_Evt  = String   -- event identifier
type ID_Cod  = String   -- function identifier
type Val     = Int      -- value

-- Special events:
-- "BOOT"

-------------------------------------------------------------------------------

checkTypes :: Type -> Type -> Bool
checkTypes TypeT           _               = True
checkTypes _               TypeT           = True
checkTypes TypeB           _               = False
checkTypes _               TypeB           = False
checkTypes (Type1 t1)      (Type1 t2)      = (t1 == t2)
checkTypes Type0           Type0           = True
checkTypes Type0           _               = False
checkTypes _               Type0           = False
checkTypes (Type1 _)       (TypeN _)       = False
checkTypes (TypeN _)       (Type1 _)       = False
checkTypes (TypeN [])      (TypeN [])      = True
checkTypes (TypeN [])      (TypeN _)       = False
checkTypes (TypeN _)       (TypeN [])      = False
checkTypes (TypeN (t1:l1)) (TypeN (t2:l2)) = (checkTypes t1 t2) && (checkTypes (TypeN l1) (TypeN l2))

checkTypesErrs :: (INode a) => a -> Type -> Type -> Errors
checkTypesErrs s t1 t2 = if checkTypes t1 t2 then [] else
                            [toError s "types do not match"]
