{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.ToSourceString.Source where

import Ceu.Grammar.Globals (Source, ToSourceString(..))

instance ToSourceString Source where
    toSourceString (_,ln,cl) = "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"
