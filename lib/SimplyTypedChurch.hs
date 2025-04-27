{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module SimplyTypedChurch where

import PreTerms
import Untyped
import Basics
import SimplyTypedCurry


import Data.List




---BEGINNINGS-----------
-- 

type RawVar = Var 
data RawTerm = R RawVar | RA RawTerm RawTerm | RL (RawVar, Type) RawTerm


freeRawVars :: RawTerm -> [Var]
freeRawVars (R x) = [x]
freeRawVars (RA m n) = freeRawVars m ++ freeRawVars n
freeRawVars (RL (x,_) m) = freeRawVars m \\ [x]



substRaw :: RawTerm -> Var -> RawTerm -> RawTerm
substRaw (R x) y n 
    | x == y = n
    | otherwise = R x
substRaw (RA p q) y n = RA (substRaw p y n) (substRaw q y n)
substRaw (RL x m) y n = undefined