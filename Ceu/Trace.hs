module Ceu.Trace where

import qualified Debug.Trace as T

traceShow   :: Show a => a -> b -> b
traceShow  = T.traceShow

traceShowId :: Show a => a -> a 
traceShowId = T.traceShowId

traceShowX :: (Show a,Show b) => a -> b -> b
traceShowX v id = traceShow (v, "==>", id) id
