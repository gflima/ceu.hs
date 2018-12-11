{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.Source where

import Ceu.Grammar.Globals (Source, Ann(..))

instance Ann Source where
    getSource (_,ln,cl) = "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"
    getN _ = 0
