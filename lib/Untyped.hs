{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Untyped where


import PreTerms
import Data.List
import Data.Maybe


---------- BEGINNINGS ----------

checkbetaRedex :: LambdaTerm -> Bool
checkbetaRedex (T (A m _)) = case T m of
    (T  (L _ _)) -> True
    _ -> False
checkbetaRedex _ = False


headRedex :: LambdaTerm -> Maybe LambdaTerm
headRedex m = case m of
    (T (A (L x p) q)) -> Just $ T $ A (L x p) q
    _ -> Nothing


checkHeaded :: LambdaTerm -> Bool
checkHeaded = isJust . headRedex


checkBetaNF :: LambdaTerm -> Bool
checkBetaNF (T m) = all (\n -> not $ checkbetaRedex n) (subTerms $ T m)



contractRedex :: LambdaTerm -> Maybe LambdaTerm
contractRedex (T (A m n)) = case m of
    L x m' -> do Just $ substTerm (T m') x (T n)
    _ -> Nothing
contractRedex _ = Nothing



-- beta-reduction with left-most strategy
betaReductionL :: LambdaTerm -> LambdaTerm
betaReductionL m
    | checkBetaNF m = m
    | otherwise =   substForTerm m redex reduced
    where -- all the from just are safe since we checked for NF, there is a redex to be contracted.
        redex = fromJust $ leftmostRedex m
        reduced = fromJust $ contractRedex $ fromJust $ leftmostRedex m

leftmostRedex :: LambdaTerm -> Maybe LambdaTerm
leftmostRedex m
    | checkbetaRedex m = Just m
    | otherwise = case m of
        (T (V _)) -> Nothing
        (T (A n r)) -> case leftmostRedex (T n) of
            Just redex -> Just redex
            Nothing -> leftmostRedex (T r)
        (T (L _ n)) -> leftmostRedex $ T n


-- Beta reduction with head-first strategy. 
betaReductionH :: LambdaTerm -> Maybe LambdaTerm
betaReductionH (T m)
    | checkHeaded (T m) = Just $ betaReductionL (T m) -- if head exists, it is the leftmost redex
    | otherwise = Nothing



-- Beta reduction with innermost-first strategy.
betaReductionI :: LambdaTerm -> LambdaTerm
betaReductionI m
    | checkBetaNF m =  m
    | otherwise =  substForTerm m redex reduced
    where -- again safe use of fromJust
        redex = fromJust $ innermostRedex m
        reduced = fromJust $ contractRedex $ fromJust $ innermostRedex m

-- Not sure if this is the right take on "innermost". Cause we prioritize the right side, which seems right when we already have left-most strategy. But what if the left-side has depth 200, and the right side depth 3? Maybe that should prioeritize left. More complicated though, i think then you have to do "a search-first, then evaluate and decide" function which is much harder
-- ChatGPT says this is ok, and actually matches a common strategy called "call-by-value evaluation". Is that right? Who knows... will I call that good enough? Yup!

innermostRedex :: LambdaTerm -> Maybe LambdaTerm
innermostRedex m
    | checkBetaNF m = Nothing
    | checkbetaRedex m && all checkBetaNF (subTerms m \\ [m]) = Just m
    | otherwise = case m of
        (T (V _)) -> Nothing
        (T (A p q)) ->
            case innermostRedex (T q) of
                Just redex -> Just redex
                Nothing -> innermostRedex (T p)
        (T (L _ body)) -> innermostRedex (T body)



-------- OTHER REDUCTIONS--------------

etaReduce :: LambdaTerm -> LambdaTerm
etaReduce m = case m of
    T(L x (A m' (V y))) | x == y && checkFreeVar x (T m') -> T m'
    _ -> m


-- Default to ReductionL because reasons.
betaEtaRed :: LambdaTerm -> LambdaTerm
betaEtaRed = betaReductionL . etaReduce


-- NOTE: potentially unsafe use of fromJust, gotta think about it.
betaReductionPar :: LambdaTerm -> LambdaTerm
betaReductionPar t
    | checkBetaNF t = t
    | otherwise = case t of
        T (V _)   -> error "this error can't hapen, covered by checkBetaNF"
        T (L x m) -> T $ L x (preTer $ betaReductionPar (T m))
        T (A m n) -> case m of
            L x p -> substTerm (T p) x (T n)
            _     -> T $ A (preTer $ betaReductionPar (T m)) (preTer $ betaReductionPar (T n))



------ MULTI REDUCTIONS ---------
-- "transitive" closures, as x-reduction repeated n-times
betaMultiReductionL :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionL m 0 = m
betaMultiReductionL m n = betaReductionL (betaMultiReductionL m (n-1))

betaMultiReductionI :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionI m 0 = m
betaMultiReductionI m n = betaReductionI (betaMultiReductionI m (n-1))

-- create a list of reduced terms.
betaReductionList ::LambdaTerm -> [LambdaTerm]
betaReductionList m =  betaReductionPar m : [betaReductionPar m]

-- itreated create a list of reduced terms.
betaMultiReductionList :: LambdaTerm -> Integer -> [LambdaTerm]
betaMultiReductionList m 0 =  [m]
betaMultiReductionList m n =  betaReductionList m ++ betaMultiReductionList m (n-1)


betaEtaMultiRed :: LambdaTerm -> Integer -> LambdaTerm
betaEtaMultiRed m 0 = m
betaEtaMultiRed m n = betaEtaRed (betaEtaMultiRed m (n-1))

betaMultiReductionPar :: LambdaTerm -> Integer -> LambdaTerm
betaMultiReductionPar m 0 = m
betaMultiReductionPar m n = betaReductionPar (betaMultiReductionPar m (n-1))



-------- COMPETE DEVELOPMENT -------------
-- By sectoin 1.7 left-strategy is normalizing. Might change to parallel to make more efficient though.
--DOUBLE CHECK: recursion done right?
completeDevelop :: LambdaTerm -> LambdaTerm
completeDevelop m =
    let recursed = betaMultiReductionL m 0
    in if checkBetaNF m
            then recursed
            else  completeDevelop $ betaMultiReductionL m 1



completeDevelopFor :: LambdaTerm -> Integer -> Maybe LambdaTerm
completeDevelopFor m a
    | checkBetaNF $ betaMultiReductionL m a = Just $ betaMultiReductionL m a
    | otherwise = Nothing -- takes longer than that to normalize"

----------------- EQUIVALENCES-------------------------

--NOTE: not sure these work properly, have to think better about wether this climbs the syntax tree properly.
-- basically, check if m == n, or if some reduction of one is == to the other, or if there's an equal r they both reduce to.
betaEq :: LambdaTerm -> LambdaTerm -> Bool
betaEq m n =
    m == n ||
    any (\x -> any (\y -> y == n) (betaMultiReductionList m x)) [0..] ||
    any (\x -> any (\y -> y == m) (betaMultiReductionList n x)) [0..] ||
    any (\x -> any (\y -> any (\m' -> any (\n' -> m' == n') (betaMultiReductionList n y)) (betaMultiReductionList m x)) [0..]) [0..]



-- do we reach beta-equivalence in n-many steps?
betaEqFor :: LambdaTerm -> LambdaTerm -> Integer ->  Maybe Bool
betaEqFor m n a = Just $
    m == n ||
    any (\x -> any (\y -> y == n) (betaMultiReductionList m x)) [0..a] ||
    any (\x -> any (\y -> y == m) (betaMultiReductionList n x)) [0..a] ||
    any (\x -> any (\y -> any (\m' -> any (\n' -> m' == n') (betaMultiReductionList n y)) (betaMultiReductionList m x)) [0..a]) [0..a]


betaEtaEq :: LambdaTerm -> LambdaTerm -> Bool
betaEtaEq m n =  any (\x -> betaEtaMultiRed m x == n ) [0..20] || any (\x -> betaEtaMultiRed m x == n ) [0..]

betaEtaEqFor:: LambdaTerm -> LambdaTerm -> Integer -> Maybe Bool
betaEtaEqFor m n a = Just $ any (\x -> betaEtaMultiRed m x == n ) [0..a] || any (\x -> betaEtaMultiRed m x == n ) [0..a]


extEq :: LambdaTerm -> LambdaTerm -> Bool
extEq = betaEtaEq

extEqFor :: LambdaTerm -> LambdaTerm -> Integer -> Maybe Bool
extEqFor = betaEtaEqFor

------------- NORMALIZATIONS -------------------
checkNormalizing :: LambdaTerm -> Bool
checkNormalizing m
    | checkBetaNF m = True
    | otherwise = any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..]


checkNormalizingFor :: LambdaTerm -> Integer -> Maybe Bool
checkNormalizingFor m a = Just $ any (\x -> checkBetaNF$ betaMultiReductionL m x) [0..a]

