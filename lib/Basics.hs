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

myReduction :: LambdaTerm
myReduction = betaMultiReductionR (bigTerm 100) 98

-- >>> prettyPrint$ myReduction
-- Maybe.fromJust: Nothing

twoRedex :: LambdaTerm
twoRedex = T $ A (L 1 (V 1)) (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))

-- >>> betaReductionL twoRedex
-- T (A (L 2 (A (V 2) (V 2))) (L 3 (V 3)))
-- >>> betaReductionL $ betaReductionL twoRedex
-- T (A (L 3 (V 3)) (L 3 (V 3)))
-- >>> betaReductionL $ betaReductionL $ betaReductionL twoRedex
-- T (L 3 (V 3))

-- >>> betaReductionR twoRedex
-- Variable not in scope:
--   betaReductionR :: LambdaTerm -> t_aaBgG[sk:1]
-- >>> betaReductionR $ betaReductionR twoRedex
-- Variable not in scope:
--   betaReductionR :: a0_aaBiY[tau:1] -> b_aaBiZ[sk:1]
-- Variable not in scope:
--   betaReductionR :: LambdaTerm -> a0_aaBiY[tau:1]
-- >>> betaReductionR $ betaReductionR $ betaReductionR twoRedex
-- Variable not in scope:
--   betaReductionR :: a1_aaBly[tau:1] -> b_aaBlz[sk:1]
-- Variable not in scope:
--   betaReductionR :: a0_aaBlC[tau:1] -> a1_aaBly[tau:1]
-- Variable not in scope:
--   betaReductionR :: LambdaTerm -> a0_aaBlC[tau:1]

-- >>>betaReductionPar twoRedex
-- T (A (L 3 (V 3)) (L 3 (V 3)))

-- >>>betaReductionPar$ betaReductionPar twoRedex
-- T (L 3 (V 3))


-- >>> completeDevelopInf (bigTerm 100)



hiddenRed :: LambdaTerm
hiddenRed =  T (A (L 1 (V 1)) (V 2)) 

-- >>>betaReductionL hiddenRed
-- T (V 2)

-- LOOPING combiY
-- >>> prettyPrint$ combiY
-- "(\\7. ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))"


-- >>> prettyPrint $ betaReductionL $ combiY
-- "(\\7. (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))"


-- >>> prettyPrint $ betaReductionL $ betaReductionL $ combiY
-- "(\\7. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\7. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\7. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"

-- >>> prettyPrint $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ betaReductionL $ combiY
-- "(\\7. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"
