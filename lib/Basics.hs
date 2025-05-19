module Basics where

import PreTerms
import Untyped



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
myCheck = checkNormalizingInf (bigTerm 100)


-- why slow now? especially when multi-reduction 100 is perfectly fast
-- >>> myCheck
-- Maybe.fromJust: Nothing

myReduction :: LambdaTerm
myReduction = betaMultiReductionL (bigTerm 100) 98

-- >>> prettyPrint$ myReduction
-- Maybe.fromJust: Nothing


-- >>> completeDevelopInf (bigTerm 100)
-- Maybe.fromJust: Nothing



twoRedex :: LambdaTerm
twoRedex = T $ A (L 1 (V 1)) (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionL twoRedex
-- T (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionL $ betaReductionL twoRedex
-- T (A (L 3 (V 3)) (L 3 (V 3)))

-- >>> betaReductionL $ betaReductionL $ betaReductionL twoRedex
-- T (L 3 (V 3))


-- >>> betaReductionI twoRedex
-- Maybe.fromJust: Nothing

-- >>> betaReductionI $ betaReductionI twoRedex
-- Maybe.fromJust: Nothing

-- >>> betaReductionI $ betaReductionI $ betaReductionI twoRedex
-- Maybe.fromJust: Nothing


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
-- >>> prettyPrint$ combiY
-- "(\\7. ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))"


-- >>> prettyPrint $ betaReductionL $ combiY
-- Maybe.fromJust: Nothing

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ combiY
-- Maybe.fromJust: Nothing

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

