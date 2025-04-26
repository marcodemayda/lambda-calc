{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Untyped where


import PreTerms

---------- BEGINNINGS ----------

checkbetaRedex :: LambdaTerm -> Bool
checkbetaRedex (T (V _)) = False
checkbetaRedex (T (L _ _)) = False
checkbetaRedex (T (A m _)) = case m of
    L _ _ -> True
    _ -> False


checkBetaNF :: LambdaTerm -> Bool
checkBetaNF (T m) = all (\n -> not $ checkbetaRedex n) (subTerms $ T m)


contractRedex :: LambdaPreTerm -> LambdaPreTerm
contractRedex ( (V m)) =  V m
contractRedex ( (L x m)) =  L x m
contractRedex ( (A m n)) = case m of
    L x m' ->   substPreTot m' x n
    _ -> A m n




-- beta-reduction with innermost-first strategy
betaReductionL :: LambdaTerm -> LambdaTerm
betaReductionL (T m)
    | checkBetaNF (T m) = T m
    | otherwise = T $ substForPreTerm m (innermostRedex (T m)) (contractRedex $ innermostRedex (T m))

innermostRedex :: LambdaTerm -> LambdaPreTerm
innermostRedex (T (V x)) = V x
innermostRedex (T (A m n))
    | not $ checkBetaNF (T m) = case m of
        V x -> V x
        A p q -> innermostRedex $ T $ A p q
        L _ _ ->  A m n
    | not $ checkBetaNF (T n) = innermostRedex $ T n
    | otherwise = A m n

innermostRedex (T (L x m))
    | not $ checkBetaNF (T m) = innermostRedex $ T m
    | otherwise = L x m



-- beta-reduction with outermost-first strategy
betaReductionR :: LambdaTerm -> LambdaTerm
betaReductionR (T m)
    | checkBetaNF (T m) = T m
    | otherwise = T $ substForPreTerm m (outermostRedex (T m)) (contractRedex $ outermostRedex (T m))


--PROBLEM: looks down a branch but doesnt go back out for potentially better options
outermostRedex :: LambdaTerm -> LambdaPreTerm
outermostRedex (T m)
    | checkbetaRedex (T m) = m
    | otherwise = case m of
        (V x) -> V x
        A n r
            | checkbetaRedex $ T r -> r
            | checkbetaRedex $ T n -> n
            | checkbetaRedex $ T $ outermostRedex $ T r -> outermostRedex $ T r
            | otherwise -> outermostRedex $ T n
        L _ n -> outermostRedex$ T n



-------- OTHER REDUCTIONS--------------
betaReductionBoth ::LambdaTerm -> [LambdaTerm]
betaReductionBoth m =  betaReductionR m : [betaReductionR m]

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

etaReduce :: LambdaTerm -> LambdaTerm
etaReduce (T m) = case m of
    L x (A m' (V y)) | x == y && checkFreePreVar x m' -> T m'
    _ -> T m

betaEtaRed :: LambdaTerm -> LambdaTerm
betaEtaRed = betaReductionR . etaReduce

betaEtaMultiRed :: LambdaTerm -> Integer -> LambdaTerm
betaEtaMultiRed m 0 = m
betaEtaMultiRed m n = betaEtaRed (betaEtaMultiRed m (n-1))


betaReductionPar :: LambdaTerm -> LambdaTerm
betaReductionPar (T (V x)) = betaReductionR $ T$ V x
betaReductionPar (T (A n r)) = betaReductionR $ T $ A (preTer $ betaReductionR $ T n) (preTer $ betaReductionR $ T r)
betaReductionPar(T (L x n)) = T $ L x (preTer $ betaReductionPar $ T n)

betaMultiReductionPar :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionPar m 0 = m
betaMultiReductionPar m n = betaReductionPar (betaMultiReductionPar m (n-1))

completeDevelop :: LambdaTerm -> LambdaTerm
completeDevelop m
    | checkBetaNF $ betaMultiReductionPar m 20 = betaMultiReductionPar m 20
    | otherwise = error "development is long"

completeDevelopInf :: LambdaTerm -> LambdaTerm
completeDevelopInf m =
    let recursed = betaMultiReductionPar m 0
    in if checkBetaNF m
            then recursed
            else  completeDevelopInf $ betaMultiReductionPar m 1

completeDevelopFor :: LambdaTerm -> Integer -> LambdaTerm
completeDevelopFor m a
    | checkBetaNF $ betaMultiReductionPar m a = betaMultiReductionPar m a
    | otherwise = error "takes longer than that to reduce"

------------ EQUIVALENCES-------------------------

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

betaEqFor :: LambdaTerm -> LambdaTerm -> Integer ->  Bool
betaEqFor m n a =
    m == n ||
    any (\x -> any (\y -> y == n) (betaMultiReductionBoth m x)) [0..a] ||
    any (\x -> any (\y -> y == m) (betaMultiReductionBoth n x)) [0..a] ||
    any (\x -> any (\y -> any (\m' -> any (\n' -> m' == n') (betaMultiReductionBoth n y)) (betaMultiReductionBoth m x)) [0..a]) [0..a]


betaEtaEq :: LambdaTerm -> LambdaTerm -> Bool
betaEtaEq m n =  any (\x -> betaEtaMultiRed m x == n ) [0..20] || any (\x -> betaEtaMultiRed m x == n ) [0..20]

betaEtaEqInf :: LambdaTerm -> LambdaTerm -> Bool
betaEtaEqInf m n =  any (\x -> betaEtaMultiRed m x == n ) [0..20] || any (\x -> betaEtaMultiRed m x == n ) [0..]

betaEtaEqFor:: LambdaTerm -> LambdaTerm -> Integer -> Bool
betaEtaEqFor m n a =  any (\x -> betaEtaMultiRed m x == n ) [0..a] || any (\x -> betaEtaMultiRed m x == n ) [0..a]


extEq :: LambdaTerm -> LambdaTerm -> Bool
extEq = betaEtaEq

extEqInf :: LambdaTerm -> LambdaTerm -> Bool
extEqInf = betaEtaEqInf

extEqFor :: LambdaTerm -> LambdaTerm -> Integer -> Bool
extEqFor = betaEtaEqFor

------------- NORMALIZATIONS
checkNormalizingInf :: LambdaTerm -> Bool
checkNormalizingInf m
    | checkBetaNF m = True
    | otherwise = any (\x -> checkBetaNF$ betaMultiReductionR m x) [0..]

checkNormalizing :: LambdaTerm -> Bool
checkNormalizing m = any (\x -> checkBetaNF$ betaMultiReductionR m x) [0..20]

checkNormalizingFor :: LambdaTerm -> Integer -> Bool
checkNormalizingFor m a = any (\x -> checkBetaNF$ betaMultiReductionR m x) [0..a]

