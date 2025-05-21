module Basics where

import PreTerms
import Untyped

import Data.Maybe



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

countVar :: Var -> LambdaTerm -> Integer
countVar x (T (V y))
    | x == y = 1
    | otherwise = 0
countVar x (T (A m n)) = countVar x (T m) + countVar x (T n)
countVar x (T (L y m))
    | x == y = 0  -- shadowed
    | otherwise = countVar x (T m)


churchNumeralFrom :: LambdaTerm -> Maybe Integer
churchNumeralFrom m
    | isChurchNumeral m = case m of
        T (L x (L _ n)) -> Just $ countVar x (T n)
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

-- >>> churchNumeralTo 5
-- T (L 0 (L 1 (A (V 0) (A (V 0) (A (V 0) (A (V 0) (A (V 0) (V 1))))))))

-- >>> churchNumeralFrom (T (L 0 (L 1 (A (V 0) (A (V 0) (A (V 0) (A (V 0) (A (V 0) (V 1)))))))))
-- Just 5




--------------------
-- TESTS
--------------------

bigTerm :: Int -> LambdaTerm
bigTerm n = T$ foldl1 A (replicate n (preTer combiId) ++ [preTer combiId])

myCheck :: Bool
myCheck = checkNormalizing (bigTerm 100)


-- why slow now? especially when multi-reduction 100 is perfectly fast
-- >>> myCheck
-- True

myReduction :: LambdaTerm
myReduction = betaMultiReductionL (bigTerm 100) 98

-- >>> prettyPrint$ myReduction
-- "(\\1. 1)"


-- >>> prettyPrint$ completeDevelop (bigTerm 100)
-- "(\\1. 1)"



twoRedex :: LambdaTerm
twoRedex = T $ A (L 1 (V 1)) (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionL twoRedex
-- T (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionL $ betaReductionL twoRedex
-- T (A (L 3 (V 3)) (L 3 (V 3)))

-- >>> betaReductionL $ betaReductionL $ betaReductionL twoRedex
-- T (L 3 (V 3))



-- >>> betaReductionI twoRedex
-- T (A (L 1 (V 1)) (A (L 3 (V 3)) (L 3 (V 3))))

-- >>> betaReductionI $ betaReductionI twoRedex
-- T (A (L 1 (V 1)) (L 3 (V 3)))

-- >>> betaReductionI $ betaReductionI $ betaReductionI twoRedex
-- T (L 3 (V 3))



-- >>> betaReductionPar twoRedex
-- T (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionPar$ betaReductionPar twoRedex
-- T (A (L 3 (V 3)) (L 3 (V 3)))

-- >>> betaReductionPar$ betaReductionPar$ betaReductionPar twoRedex
-- T (L 3 (V 3))



hiddenRed :: LambdaTerm
hiddenRed =  T (A (L 1 (V 1)) (V 2))

-- >>>betaReductionL hiddenRed
-- T (V 2)


-- LOOPING combiY

-- this takes way too long, it's either very inefficient or looping.

-- takes way too long, clearly something is wrong. Might be looping
mySubst :: LambdaTerm
mySubst = substForTerm combiY (fromJust $ leftmostRedex combiY) (fromJust $ contractRedex $ fromJust $ leftmostRedex combiY)


myPreSubst :: Maybe LambdaPreTerm
myPreSubst = substForPreTerm myalconv (preTer $ fromJust $ leftmostRedex combiY) (preTer $ fromJust $ contractRedex $ fromJust $ leftmostRedex combiY)
-- >>> myPreSubst
-- Prelude.head: empty list



myalconv :: LambdaPreTerm
myalconv = alphaConvFor (preTer combiY) (preTer $ fromJust $ contractRedex $ fromJust $ leftmostRedex combiY)
-- >>> myalconv
-- L 2 (A (L 1 (A (V 2) (A (V 1) (V 1)))) (L 1 (A (V 2) (A (V 1) (V 1)))))
-- >>> preTer combiY
-- L 7 (A (L 1 (A (V 7) (A (V 1) (V 1)))) (L 1 (A (V 7) (A (V 1) (V 1)))))



check = checkSubstForIllDefined (myalconv) (preTer $ fromJust $ leftmostRedex combiY) (preTer $ fromJust $ contractRedex $ fromJust $ leftmostRedex combiY)
-- >>> check
-- False

subtermcode :: [[Int]]
subtermcode = getSubtermCodes (T myalconv)  (fromJust $ leftmostRedex combiY)
-- >>>subtermcode
-- []

leftredex :: Maybe LambdaTerm
leftredex = leftmostRedex combiY
-- >>> leftredex
-- Just (T (A (L 1 (A (V 7) (A (V 1) (V 1)))) (L 1 (A (V 7) (A (V 1) (V 1))))))

subterm :: Bool
subterm = fromJust leftredex `elem` subTerms (T myalconv)
-- >>> subterm
-- False

-- that was the problem. Once we alpha convert, we lose sub-(Pre)Term condition. Must re-do things for terms so that we have alpha equivalence equality.
-- I have now tentatively done it, seems to work but needs double-checking


code :: [[Int]]
code = getSubtermCodes (T (L 1 (A (V 1) (L 2 (V 2))))) (T (L 3 (V 3)))
-- >>> code
-- [[0,2]]



-- >>> prettyPrint$ combiY
-- "(\\7. ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))"

-- >>> prettyPrint $ betaReductionL $ combiY
-- "(\\2. (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))"


-- >>> prettyPrint $ betaReductionL $ betaReductionL $ combiY
-- "(\\2. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\2. (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\2. (7 (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\2. (7 (7 (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))))))"


parallelTest :: LambdaTerm
parallelTest = T$ A (preTer combiOm) (A (preTer combiId) (preTer combiId))

{-
Mimiking the example in the book. Internal(or right-most) should converge to IdId in two steps
Left-most should take 3, whilst the gap can be closed back to 2 with parallel reduction
-}
-- >>> prettyPrint parallelTest
-- "((\\1. (1 1)) ((\\1. 1) (\\1. 1)))"


-- >>> prettyPrint $ (betaMultiReductionI parallelTest 1)
-- "((\\1. (1 1)) (\\1. 1))"

-- >>> prettyPrint $ (betaMultiReductionI parallelTest 2)
-- "((\\1. 1) (\\1. 1))"



-- >>> prettyPrint $ (betaMultiReductionL parallelTest 1)
-- "(((\\1. 1) (\\1. 1)) ((\\1. 1) (\\1. 1)))"

-- >>> prettyPrint $ (betaMultiReductionL parallelTest 2)
-- "((\\1. 1) ((\\1. 1) (\\1. 1)))"

-- >>> prettyPrint $ (betaMultiReductionL parallelTest 3)
-- "((\\1. 1) (\\1. 1))"


-- >>> prettyPrint $ (betaMultiReductionL parallelTest 1)
-- "(((\\1. 1) (\\1. 1)) ((\\1. 1) (\\1. 1)))"

-- >>> prettyPrint $ (betaMultiReductionPar parallelTest 2)
-- "((\\1. 1) (\\1. 1))"


--------------
-- >>> prettyPrint $ churchNumeralTo 5
-- "(\\0. (\\1. (7 (7 (7 (7 (7 1)))))))"


