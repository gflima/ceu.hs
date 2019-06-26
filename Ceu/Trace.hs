module Ceu.Trace where

import qualified Debug.Trace as T

traceShow   :: Show a => a -> b -> b
traceShowId :: Show a => a -> a 

traceShow       = T.traceShow
traceShowId     = T.traceShowId
traceShowX v id = traceShow (v, "==>", id) id
