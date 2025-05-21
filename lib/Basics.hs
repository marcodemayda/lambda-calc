module Basics where

import PreTerms
import Untyped

import Data.Maybe
import GHC.Num (integerFromInt)
import Data.List (genericLength)



--------------------
-- COMBINATORS
--------------------

combiId :: LambdaTerm
combiId = T$ L 1 (V 1)

combiK :: LambdaTerm
combiK = T$ L 1 (L 2 (V 1))

combiS :: LambdaTerm
combiS = T$ L 1 (L 2 (L 3 (A (A (V 1) (V 3)) (A (V 2) (V 3)))))

combiOm :: LambdaTerm
combiOm = T$ L 1 (A (V 1) (V 1))

combiOM :: LambdaTerm
combiOM = T$ A (preTer combiOm) (preTer combiOm)

combiY :: LambdaTerm
combiY = T$ L 7 (A (L 1 (A (V 7) (A (V 1) (V 1)))) (L 1 (A (V 7) (A (V 1) (V 1)))))



--------------------
-- ENCODING FUNCTIONS
--------------------

verum :: LambdaTerm
verum = T $ L 1 (L 2 (V 1))

falsum :: LambdaTerm
falsum = T $ L 1 (L 2 (V 2))


ifThenElse :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> LambdaTerm
ifThenElse p q r = T $ A p (A q r)



pair :: LambdaPreTerm -> LambdaPreTerm -> LambdaTerm
pair m n = T $ L 1 (A (V 1) (A m n))

pi1 :: LambdaPreTerm
pi1 = L 9 (A (V 9) (preTer verum))

pi2 :: LambdaPreTerm
pi2 =  L 9 (A (V 9) (preTer falsum))

pi1App :: LambdaPreTerm -> LambdaPreTerm
pi1App = A pi1

pi2App :: LambdaPreTerm -> LambdaPreTerm
pi2App = A pi2


-- apply m to n x-many times
repeatApplication ::  LambdaPreTerm -> LambdaPreTerm -> Integer -> LambdaPreTerm
repeatApplication m n 0 = A m n
repeatApplication m n x = A m (repeatApplication m n (x-1))


churchNumeralTo :: Integer -> LambdaTerm
churchNumeralTo 0 = T$ L 0 $ L 1 (V 1)
churchNumeralTo n = T$ L 0 $ L 1 (repeatApplication (V 0) (V 1) (n-1))


isChurchNumeral :: LambdaTerm -> Bool
isChurchNumeral (T (L f (L x m))) = checkBody m
  where
    checkBody (V y) = y == x
    checkBody (A p q) = p == V f && checkBody q
    checkBody _ = False
isChurchNumeral _ = False


churchNumeralFrom :: LambdaTerm -> Maybe Integer
churchNumeralFrom m
    | isChurchNumeral m = case m of
        T (L _ (L y n)) -> Just $ genericLength $ head $ getSubtermCodes (T n) (T (V y)) 
        _ -> Nothing -- impossible case, covered by isChurchNumeral
    | otherwise = Nothing


suc :: LambdaTerm
suc = T$ L 4 $ L 7 $ L 1 (A (V 7) (A (V 4) (A (V 7) (V 1))))

succApp :: LambdaTerm -> LambdaTerm
succApp m = T $ A (preTer suc) (preTer m) -- bit ugly to have to pre-term...

add :: LambdaTerm
add = T $ L 4 $ L 5 $ L 7 $ L 1 (A (V 5) (A (V 7) (A (V 4) (A (V 7) (V 1)))))

addApp :: LambdaTerm -> LambdaTerm -> LambdaTerm
addApp (T m) (T n) = T $ A (preTer add) (A m n) -- again, bit ugly



--------------------
-- TESTS
--------------------


-- >>> churchNumeralTo 5
-- T (L 0 (L 1 (A (V 0) (A (V 0) (A (V 0) (A (V 0) (A (V 0) (V 1))))))))

-- >>> churchNumeralFrom (churchNumeralTo 2)
-- Just 2


-- >>>betaReductionL $ betaReductionL $ betaReductionL $ addApp (churchNumeralTo 5) (churchNumeralTo 5)
-- ProgressCancelledException
