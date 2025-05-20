module Basics where

import PreTerms
import Untyped

import Data.Maybe



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
-- T (A (L 3 (V 3)) (L 3 (V 3)))

-- >>> betaReductionI $ betaReductionI twoRedex
-- T (L 3 (V 3))

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

-- that's the problem. Once we alpha convert, we lose sub-PreTerm condition. Must re-do things for terms so that we have alpha equivalence equality.


code :: [[Int]]
code = getSubtermCodes (T (L 1 (A (V 1) (L 2 (V 2))))) (T (L 3 (V 3)))
-- >>> code
-- [[0,2]]


-- >>> prettyPrint$ combiY
-- "(\\7. ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))"

-- >>> prettyPrint $ betaReductionL $ combiY
-- Prelude.head: empty list


-- >>> prettyPrint $ betaReductionL $ betaReductionL $ combiY
-- Prelude.head: empty list

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- Maybe.fromJust: Nothing

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- Maybe.fromJust: Nothing

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- Maybe.fromJust: Nothing


parallelTest :: LambdaTerm
parallelTest = T$ A (preTer combiOm) (A (preTer combiId) (preTer combiId))

{-
Mimiking the example in the book. Internal(or right-most) should converge to IdId in two steps
Left-most should take 3, whilst the gap can be closed back to 2 with parallel reduction
-}
-- >>> prettyPrint parallelTest
-- "((\\1. (1 1)) ((\\1. 1) (\\1. 1)))"


-- >>> prettyPrint $ (betaMultiReductionI parallelTest 1)
-- Maybe.fromJust: Nothing

-- >>> prettyPrint $ (betaMultiReductionI parallelTest 2)
-- Maybe.fromJust: Nothing



-- >>> prettyPrint $ (betaMultiReductionL parallelTest 1)
-- "(((\\1. 1) (\\1. 1)) ((\\1. 1) (\\1. 1)))"

-- >>> prettyPrint $ (betaMultiReductionL parallelTest 2)
-- Maybe.fromJust: Nothing

-- >>> prettyPrint $ (betaMultiReductionL parallelTest 3)
-- Maybe.fromJust: Nothing


-- >>> prettyPrint $ (betaMultiReductionL parallelTest 1)
-- "(((\\1. 1) (\\1. 1)) ((\\1. 1) (\\1. 1)))"

-- >>> prettyPrint $ (betaMultiReductionPar parallelTest 2)
-- "((\\1. 1) (\\1. 1))"

