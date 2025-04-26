{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Redundant case" #-}
module Untyped where


import PreTerms
import Control.Monad.State

---------- BEGINNINGS ----------

checkbetaRedex :: LambdaTerm -> Bool
checkbetaRedex (T (V _)) = False
checkbetaRedex (T (L _ _)) = False
checkbetaRedex (T (A m _)) = case m of
    L _ _ -> True
    _ -> False


checkBetaNF :: LambdaTerm -> Bool
checkBetaNF m = all (\n -> contractRedex n == n) (subPreTerms $ preTer m)


contractRedex :: LambdaPreTerm -> LambdaPreTerm
contractRedex ( (V m)) =  (V m)
contractRedex ( (L x m)) =  (L x m)
contractRedex ( (A m n)) = case m of
    L x m' ->   substPreTot m' x n
    _ -> A m n




-- beta-reduction with innermost-first strategy
betaReductionL :: LambdaTerm -> LambdaTerm
betaReductionL = T . contractRedex . innermostRedex

innermostRedex :: LambdaTerm -> LambdaPreTerm
innermostRedex = undefined



-- beta-reduction with outermost-first strategy
betaReductionR :: LambdaTerm -> LambdaTerm
betaReductionR (T m) = T $ substForPreTerm m (outermostRedex (T m)) (contractRedex $ outermostRedex (T m))

outermostRedex :: LambdaTerm -> LambdaPreTerm
outermostRedex (T m)
    | checkbetaRedex (T m) = m
    | otherwise = case m of
        (V x) -> V x
        A n r
            | checkbetaRedex$ T n -> outermostRedex$ T n
            | otherwise -> outermostRedex$ T r
        L _ n -> outermostRedex$ T n



betaReductionBoth ::LambdaTerm -> [LambdaTerm]
betaReductionBoth m =  betaReductionL m : [betaReductionR m]

-- "transitive" closure as beta-reduction repeated n-times
betaMultiReductionL :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionL m 0 = m
betaMultiReductionL m n = betaReductionL (betaMultiReductionL m (n-1))

betaMultiReductionR :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionR m 0 = m
betaMultiReductionR m n = betaReductionR (betaMultiReductionR m (n-1))


betaMultiReductionBoth :: LambdaTerm -> Integer -> [LambdaTerm]
betaMultiReductionBoth m 0 =  [m]
betaMultiReductionBoth m n =  betaReductionBoth m ++ betaMultiReductionBoth m (n-1)


-- basically, check if m == n, or if some reduction of one is == to the other, or if there's an equal r they both reduce to.
betaEqInf :: LambdaTerm -> LambdaTerm -> Bool
betaEqInf m n =
    m == n ||
    any (\x -> any (\y -> y == n) (betaMultiReductionBoth m x)) [0..] ||
    any (\x -> any (\y -> y == m) (betaMultiReductionBoth n x)) [0..] ||
    any (\x -> any (\y -> any (\m' -> any (\n' -> m' == n') (betaMultiReductionBoth n y)) (betaMultiReductionBoth m x)) [0..]) [0..]


betaEq :: LambdaTerm -> LambdaTerm -> Bool
betaEq m n =
    m == n ||
    any (\x -> any (\y -> y == n) (betaMultiReductionBoth m x)) [0..20] ||
    any (\x -> any (\y -> y == m) (betaMultiReductionBoth n x)) [0..20] ||
    any (\x -> any (\y -> any (\m' -> any (\n' -> m' == n') (betaMultiReductionBoth n y)) (betaMultiReductionBoth m x)) [0..20]) [0..20]


etaReduce :: LambdaTerm -> LambdaTerm
etaReduce (T m) = case m of
    L x (A m' (V y)) | x == y && checkFreePreVar x m' -> T m'
    _ -> T m



betaEtaRed :: LambdaTerm -> LambdaTerm
betaEtaRed = betaReductionL . etaReduce

betaEtaMultiRed :: LambdaTerm -> Integer -> LambdaTerm
betaEtaMultiRed m 0 = m
betaEtaMultiRed m n = betaEtaRed (betaEtaMultiRed m (n-1))


betaEtaEq :: LambdaTerm -> LambdaTerm -> Bool
betaEtaEq m n =  any (\x -> betaEtaMultiRed m x == n ) [0..20] || any (\x -> betaEtaMultiRed m x == n ) [0..20]



extEq :: LambdaTerm -> LambdaTerm -> Bool
extEq = betaEtaEq


betaParReduction :: LambdaTerm -> LambdaTerm
betaParReduction (T m) = case m of
    (V x) -> betaReductionL$ T$ V x
    (A n r) -> T$ A (preTer $ betaReductionL (T n)) (preTer $ betaReductionL (T r))
    (L x n) -> case n of
        _ -> undefined

completeDevelop :: LambdaTerm -> LambdaTerm
completeDevelop = undefined


checkNormalizingInf :: LambdaTerm -> Bool
checkNormalizingInf m = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..]

checkNormalizing :: LambdaTerm -> Bool
checkNormalizing m = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..20]
