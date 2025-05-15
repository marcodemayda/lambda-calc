{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module SimplyTypedChurch where


import PreTerms
import SimplyTypedCurry


import Data.List




---BEGINNINGS-----------
-- 

type RawVar = Var
data RawTerm = R RawVar | RA RawTerm RawTerm | RL (RawVar, ArType) RawTerm
    deriving (Eq,Show)
--NOTE: to do, gotta tranlate all the work for terms to RawTerms to get alpha equivalence.

freeRawVars :: RawTerm -> [Var]
freeRawVars (R x) = [x]
freeRawVars (RA m n) = freeRawVars m ++ freeRawVars n
freeRawVars (RL (x,_) m) = freeRawVars m \\ [x]



substRaw :: RawTerm -> Var -> RawTerm -> RawTerm
substRaw (R x) y n
    | x == y = n
    | otherwise = R x
substRaw (RA p q) y n = RA (substRaw p y n) (substRaw q y n)
substRaw (RL y m) x n
    | x /= fst y && notElem x (freeRawVars n) = RL y (substRaw m x n)
    | otherwise = RL y m



-------------------------- Judgmetns -----------------------

type JudgmentCh = (Context, (RawTerm, ArType))

inferChurchVAR :: JudgmentCh -> Bool
inferChurchVAR (ga, (ra, t)) = any (\(x,y) -> (R x,y) == (ra,t)) ga

inferChurchABS :: JudgmentCh -> JudgmentCh -> Bool
inferChurchABS (ga1, (la1,t1)) (ga2, (la2,t2)) = case la2 of
    (RL x m) ->  case t2 of
        si `To` ta -> snd x == si
                            && t1 == ta
                            && ga2 == ga1 \\ [(fst x, si)]
                            && la1 == m
        _ -> False
    _ -> False


inferChurchAPP :: JudgmentCh -> JudgmentCh -> JudgmentCh ->  Bool
inferChurchAPP (ga1, (la1, t1)) (ga2, (la2,t2)) (ga3, (la3, t3)) =
    case t1 of
        ta `To` si -> ga1 == ga2 && ga2 == ga3
                    && la3 ==  RA la1 la2
                    && t2 == si && t3 == ta
        _ -> False





---- OTHER FUNCTIONS --------

churchToPre :: RawTerm -> LambdaPreTerm
churchToPre (R x) = V x
churchToPre (RA m n) = A (churchToPre m) (churchToPre n)
churchToPre (RL x m) = L (fst x) (churchToPre m)


churchToCurry :: RawTerm -> LambdaTerm
churchToCurry = T . churchToPre