module Ceu.Grammar.Type where

import Ceu.Grammar.Globals

data Type = TypeB
          | TypeT
          | Type0
          | Type1 ID_Type
          | TypeN [Type]    -- (len >= 2)
    deriving (Eq,Show)

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

