{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Untyped where


import PreTerms
import Data.List
import Text.Read
import Data.Maybe
import Language.Haskell.TH.Syntax (nothingName)

---------- BEGINNINGS ----------

checkbetaRedex :: LambdaTerm -> Bool
checkbetaRedex (T (A m _)) = case m of
    L _ _ -> True
    _ -> False
checkbetaRedex _ = False


headRedex :: LambdaTerm -> Maybe LambdaPreTerm
headRedex (T m)= case m of
    A (L x p) q -> Just $ A (L x p) q
    _ -> Nothing

checkHeaded :: LambdaTerm -> Bool
checkHeaded = isJust . headRedex


checkBetaNF :: LambdaTerm -> Bool
checkBetaNF (T m) = all (\n -> not $ checkbetaRedex n) (subTerms $ T m)



contractRedex :: LambdaPreTerm -> Maybe LambdaPreTerm
contractRedex ( (A m n)) = case m of
    L x m' -> do substPreTerm m' x n
    _ -> Nothing
contractRedex _ = Nothing



-- beta-reduction with left-most strategy
betaReductionL :: LambdaTerm -> LambdaTerm
betaReductionL (T m)
    | checkBetaNF (T m) = T m
    | otherwise = T $ fromJust $ substForPreTerm m (fromJust $ leftmostRedex (T m)) (fromJust $ contractRedex $ fromJust $ leftmostRedex (T m))


leftmostRedex :: LambdaTerm -> Maybe LambdaPreTerm
leftmostRedex (T m)
    | checkbetaRedex (T m) = Just m
    | otherwise = case m of
        (V _) -> Nothing
        A n r -> case leftmostRedex (T n) of
            Just redex -> Just redex
            Nothing -> leftmostRedex (T r)
        L _ n -> leftmostRedex $ T n


-- Beta reduction with head-first strategy. 
betaReductionH :: LambdaTerm -> Maybe LambdaTerm
betaReductionH (T m)
    | checkHeaded (T m) = Just $ betaReductionL (T m)
    | otherwise = Nothing


-- Beta reduction with innermost-first strategy.
betaReductionI :: LambdaTerm -> LambdaTerm
betaReductionI (T m)
    | checkBetaNF (T m) = T m
    | otherwise = T $ fromJust $ substForPreTerm m (fromJust $ innermostRedex (T m)) (fromJust $ contractRedex $ fromJust $ innermostRedex (T m))


-- Not sure if this is the right take on "innermost". Cause we prioritize the right side, which seems right when we already have left-most strategy. But what if the left-side has depth 200, and the right side depth 3? Maybe that should prioeritize left. More complicated though, i think then you have to do "a search-first, then evaluate and decide" function which is much harder
-- ChatGPT says this is ok, and actually matches a common strategy called "call-by-value evaluation". Is that right? Who knows... will I call that good enough? Yup!
innermostRedex :: LambdaTerm -> Maybe LambdaPreTerm
innermostRedex (T m)
    | checkBetaNF (T m) = Nothing
    | checkbetaRedex (T m) && any checkBetaNF (map T (subPreTerms m) \\ [T m]) = Just m
    | otherwise = case m of
        V _ -> Nothing
        A p q ->
            case innermostRedex (T q) of
                Just red -> Just red
                Nothing -> innermostRedex (T p)
        L _ body -> innermostRedex (T body)



-------- OTHER REDUCTIONS--------------

-- "transitive" closure as beta-reduction repeated n-times
betaMultiReductionL :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionL m 0 = m
betaMultiReductionL m n = betaReductionL (betaMultiReductionL m (n-1))

betaMultiReductionI :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionI m 0 = m
betaMultiReductionI m n = betaReductionL (betaMultiReductionI m (n-1))


betaReductionBoth ::LambdaTerm -> [LambdaTerm]
betaReductionBoth m =  betaReductionL m : [betaReductionL m]

betaMultiReductionBoth :: LambdaTerm -> Integer -> [LambdaTerm]
betaMultiReductionBoth m 0 =  [m]
betaMultiReductionBoth m n =  betaReductionBoth m ++ betaMultiReductionBoth m (n-1)

etaReduce :: LambdaTerm -> LambdaTerm
etaReduce (T m) = case m of
    L x (A m' (V y)) | x == y && checkFreePreVar x m' -> T m'
    _ -> T m

betaEtaRed :: LambdaTerm -> LambdaTerm
betaEtaRed = betaReductionL . etaReduce

betaEtaMultiRed :: LambdaTerm -> Integer -> LambdaTerm
betaEtaMultiRed m 0 = m
betaEtaMultiRed m n = betaEtaRed (betaEtaMultiRed m (n-1))


betaReductionPar :: LambdaTerm -> LambdaTerm
betaReductionPar = undefined

betaMultiReductionPar :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionPar m 0 = m
betaMultiReductionPar m n = betaReductionL (betaMultiReductionL m (n-1))


-- By sectoin 1.7 left-strategy is normalizing. Might change to parallel to make more efficient though.
completeDevelop :: LambdaTerm -> LambdaTerm
completeDevelop m
    | checkBetaNF $ betaMultiReductionL m 20 = betaMultiReductionL m 20
    | otherwise = error "normal form is far (more than 20)"

completeDevelopInf :: LambdaTerm -> LambdaTerm
completeDevelopInf m =
    let recursed = betaMultiReductionL m 0
    in if checkBetaNF m
            then recursed
            else  completeDevelopInf $ betaMultiReductionL m 1

completeDevelopFor :: LambdaTerm -> Integer -> LambdaTerm
completeDevelopFor m a
    | checkBetaNF $ betaMultiReductionL m a = betaMultiReductionL m a
    | otherwise = error "takes longer than that to normalize"

------------ EQUIVALENCES-------------------------

--NOTE: not sure these work properly, have to think better about wether this climbs the syntax tree properly.
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
    | otherwise = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..]

checkNormalizing :: LambdaTerm -> Bool
checkNormalizing m = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..20]

checkNormalizingFor :: LambdaTerm -> Integer -> Bool
checkNormalizingFor m a = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..a]

