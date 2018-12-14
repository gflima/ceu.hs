{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.Source where

import Ceu.Grammar.Globals (Source, Ann(..))

instance Ann Source where
    getSource src = Just src
    getN _ = 0