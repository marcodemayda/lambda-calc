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




bigTerm :: Int -> LambdaPreTerm
bigTerm n = foldl1 A (replicate n (preTer combiId) ++ [preTer combiId])

myCheck :: Bool
myCheck = checkNormalizingInf (T $ bigTerm 10)

myReduction :: LambdaTerm
myReduction = betaMultiReductionR (T $ bigTerm 500) 150

-- >>> myReduction
-- ProgressCancelledException




-- >>> outermostRedex$ T (A (A (A (L 1 (V 1)) (L 1 (V 1))) (L 1 (V 1))) (L 1 (V 1)))
-- A (L 1 (V 1)) (L 1 (V 1))

-- >>> prettyPrint$ combiY
-- "(\\7. ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))"

-- >>> prettyPrint $ betaReductionR $ combiY
-- "(\\7. (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))"


-- >>> prettyPrint$ betaReductionR $ betaReductionR $ combiY
-- "(\\7. (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))"


-- >>> prettyPrint$ betaReductionR $ betaReductionR $ betaReductionR $ combiY
-- "(\\7. (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))))"



-- >>> prettyPrint $ betaReductionR $ betaReductionR $ betaReductionR $ betaReductionR $ combiY
-- "(\\7. (7 (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1)))))))))"


-- >>> prettyPrint $ betaReductionR $ betaReductionR $ betaReductionR $ betaReductionR $ betaReductionR $ combiY
-- "(\\7. (7 (7 (7 (7 (7 ((\\1. (7 (1 1))) (\\1. (7 (1 1))))))))))"


--LETS FUCKING GO!!
