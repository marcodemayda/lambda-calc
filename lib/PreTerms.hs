{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module PreTerms where


import Data.Maybe
import Data.List
-- import MissingH Data.List.Utils


---------- PRE TERMS ----------
type Var = Integer

variables :: [Var]
variables = [1..]


data LambdaPreTerm =  V Var | A LambdaPreTerm LambdaPreTerm  | L Var LambdaPreTerm
    deriving (Show, Eq)


-- lists free variables in a Pre-term
freePreVars :: LambdaPreTerm -> [Var]
freePreVars (V x) = [x]
freePreVars (L x m) = [y | y <- freePreVars m,  y /= x]
freePreVars (A m n) = nub $ freePreVars m ++ freePreVars n

-- check if x is a freevariable of Pre-term n
checkFreePreVar :: Var -> LambdaPreTerm -> Bool
checkFreePreVar x n = x `elem` freePreVars n

-- list all variables of a term
variablesPreOf :: LambdaPreTerm -> [Var]
variablesPreOf (V x) = [x]
variablesPreOf (A m n) = nub $ variablesPreOf m ++ variablesPreOf n
variablesPreOf (L _ m) = variablesPreOf m

-- grab a variable not appearing in the term
freshPreVar :: LambdaPreTerm -> Var
freshPreVar m = head $ variables \\ variablesPreOf m

-- a vector of \x\y\z... M
lambdaVec :: [Var] -> LambdaPreTerm -> LambdaPreTerm
lambdaVec xs m = foldr L m xs




-------------- SUBSTITUTIONS -------------------------
cartProd :: [a] -> [b] -> [(a, b)]
cartProd xs ys = [(x,y) | x <- xs, y <- ys]

isAbsWith :: LambdaPreTerm -> Var -> Bool
isAbsWith m y = case m of
    L z _
        | z == y -> True
        | otherwise -> False
    _ -> False


checkSubstIllDefined :: LambdaPreTerm -> Var -> LambdaPreTerm -> Bool
checkSubstIllDefined m x n = any (\(m',y)-> checkFreePreVar x m' && isAbsWith m y && y `elem` freePreVars n ) (cartProd (subPreTerms m) (freePreVars m))

-- substitution for Pre-terms, read "Pre-term with Var substituted for Pre-term"
substPreTerm :: LambdaPreTerm -> Var -> LambdaPreTerm -> Maybe LambdaPreTerm
substPreTerm m x n
    | checkSubstIllDefined m x n  = Nothing
    | otherwise = case m of
        V y
            | y==x -> Just n
            | otherwise -> Just $ V y
        A p q -> do
            p' <- substPreTerm p x n
            q' <- substPreTerm q x n
            return $ A p' q'
        L y p
            | y ==x -> Just $ L y p
            | otherwise -> do
                p' <- substPreTerm p x n
                return $ L y p'

-- old version
-- substPreTerm (V y) x n
--     | y /= x    = Just (V y)
--     | otherwise = Just n
-- substPreTerm (A p q) x n = do
--     p' <- substPreTerm p x n
--     q' <- substPreTerm q x n
--     return $ A p' q'
-- substPreTerm (L y p) x n
--     | checkFreePreVar x (L y p) && checkFreePreVar y n = Nothing -- Variable capture (see definition 1.2.4)
--     | x /= y && not (checkFreePreVar y n && checkFreePreVar x p) = do
--         p' <- substPreTerm p x n
--         return $ L y p'
--     | otherwise = Just $ L y p




countElem :: Eq a => a -> [a] -> Int
countElem i = length . filter (i==)

checkSubstForIllDefined :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> Bool
checkSubstForIllDefined m p n = 
    p `elem` subPreTerms m && -- p is a sub-term
    countElem p (subPreTerms m) == 1 && 
    False -- p is uniqe in m
    
-- change an entire sub-term. read "preTerm M with sub-term p substituted for preTerm q".
-- NOTE: the intended use is when the term being substituted can be uniquely identitfied, as this substitutes for only one occurence of the sub-term
-- substForPreTerm :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> Maybe LambdaPreTerm
-- substForPreTerm m p n
--     | checkSubstForIllDefined m p n = Nothing
--     | otherwise = undefined


-- old verions
substForPreTerm :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> Maybe LambdaPreTerm
substForPreTerm m (V x) q = substPreTerm m x q

substForPreTerm (V _) (A _ _) _         = Nothing
substForPreTerm (V _) (L _ _) _         = Nothing

substForPreTerm (A j k) (A p r) q
    | A j k == A p r                    = Just q
    | A p r `elem` subPreTerms j        =
        do
            j' <- substForPreTerm j (A p r) q
            return $ A j' k
    | A p r `elem` subPreTerms k        =
        do
            k' <- substForPreTerm k (A p r) q
            return $ A j k'
    | otherwise                         = Nothing


substForPreTerm (L x k) (A p r) q
    | A p r `elem` subPreTerms k  -- && x `notElem` freePreVars k -- unsure about this part. Including it seems to make examples not work. But a priori i'd think it needs ot be included.
                                        = do L x <$> substForPreTerm k (A p r) q
    | otherwise                         = Nothing


substForPreTerm (A j k) (L y r) q
    | L y r `elem` subPreTerms j        = do
                                            j' <- substForPreTerm j (L y r) q
                                            return $ A j' k
    | L y r `elem` subPreTerms k        = do
                                            k' <- substForPreTerm k (L y r) q
                                            return $ A j k'
    | otherwise                         = Nothing
substForPreTerm (L x s) (L y r) q
    | L x s == L y r                    = Just q
    | L y r `elem` subPreTerms (L x s)  = L x <$> substForPreTerm s (L y r) q
    | otherwise                         = Nothing



-- alpha conevrt Term with Variable
alphaConv :: LambdaPreTerm -> Var -> Maybe LambdaPreTerm
alphaConv (V _) _ = Nothing
alphaConv (L x m) y
    | checkFreePreVar y m = Nothing
    | otherwise = do
        m' <- substPreTerm m x (V y)
        return$ L y m'
alphaConv (A _ _) _ = Nothing


-- alpha convert m so as to make it compatible for substitution with n
-- DOUBLE CHECK
alphaConvFor :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm
alphaConvFor m n = case alphaConv m (freshPreVar n) of
    Just m' -> m'
    _ -> error "i'm not sure what to do yet or if this is possible"


alphaEq :: LambdaPreTerm -> LambdaPreTerm -> Bool
alphaEq (V x) (V y) = x == y
alphaEq (A m1 n1) (A m2 n2) = alphaEq m1 m2 && alphaEq n1 n2
alphaEq (L x m) (L y n)
    | x == y = alphaEq m n
    | otherwise = case alphaConv (L x m) y of
                    Just (L _ m') -> alphaEq m' n
                    _        -> False
alphaEq _ _ = False



---------- LAMBDA TERMS ----------
newtype LambdaTerm = T LambdaPreTerm
    deriving (Show)

instance Eq LambdaTerm where
    (==) :: LambdaTerm -> LambdaTerm -> Bool
    T m == T n = alphaEq m n

-- lists free variables in a Term
freeVars :: LambdaTerm -> [Var]
freeVars (T m)= freePreVars m

-- check if x is a freevariable of Term n
checkFreeVar :: Var -> LambdaTerm -> Bool
checkFreeVar x (T m) = x `elem` freePreVars m

-- list all variables of a term
variablesOf :: LambdaTerm -> [Var]
variablesOf (T (V x)) = [x]
variablesOf (T (A m n)) = nub $ variablesPreOf m ++ variablesPreOf n
variablesOf (T (L _ m)) = variablesPreOf m

-- grab a new variable not in the term
freshVar :: LambdaTerm -> Var
freshVar m = head $ variables \\ variablesOf m


-- again read "Term with Var substituted for Term"
substTerm :: LambdaTerm -> Var -> LambdaTerm -> Maybe LambdaTerm
substTerm (T m) x (T n) = do
    t <- substPreTerm m x n
    return $ T t


---------- MORE FUNCTIONS ----------


-- check if a term is a combinator, i.e. closed
checkCombinator :: LambdaTerm -> Bool
checkCombinator (T m) = null (freePreVars m)


-- map function over syntax tree
--DOUBLE CHECK
mapPreTerm :: (LambdaPreTerm -> LambdaPreTerm) -> LambdaPreTerm -> LambdaPreTerm
mapPreTerm f (V x) = f (V x)
mapPreTerm f (A m n) = f$ A (mapPreTerm f m) (mapPreTerm f n)
mapPreTerm f (L x m) = f$ L x (mapPreTerm f m)

-- as above
mapTerm :: (LambdaPreTerm -> LambdaPreTerm) -> LambdaTerm -> LambdaTerm
mapTerm f (T m) = T$ mapPreTerm f m

-- list of sub-(pre) terms
subPreTerms :: LambdaPreTerm -> [LambdaPreTerm]
subPreTerms (V x) = [V x]
subPreTerms (A m n) = A m n : subPreTerms m ++  subPreTerms n
subPreTerms (L x m) = L x m : subPreTerms m

subTerms :: LambdaTerm -> [LambdaTerm]
subTerms (T m) = map T (subPreTerms m)

-- make a term into a pre-term
preTer :: LambdaTerm -> LambdaPreTerm
preTer (T m) = m


------------- TOTAL FUNCTIONS -----------------
--------(of functions that aren't already)--------
-- should account for variable capture with alpha-conversion... not sure it does as of yet.


-- converts to alpha equivalent instead of failing
-- substPreTermTot :: LambdaPreTerm -> Var -> LambdaPreTerm -> LambdaPreTerm
-- substPreTermTot m x n= case substPreTerm m x n of
--     Just m' -> m'
--     _ -> substPreTermTot (alphaConvTot m (newVar)) () n


-- -- DOUBLE CHECK
-- alphaConvTot:: LambdaPreTerm -> Var -> LambdaPreTerm
-- alphaConvTot (L x m) = case alphaConv (L x m) (head $ freePreVars (L x m)) of
--     Just n -> n
--     Nothing -> error "stuff"
-- alphaConvTot m = m





substForPreTermTot :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm
substForPreTermTot m p q = case substForPreTerm m p q of
    Just m' -> m'
    Nothing -> case substForPreTerm (alphaConvFor m p) p q of
        Just t -> t
        _ -> error "this shoudln't happen"




---------- PRETTY PRINTS ----------
-- print Pre-term as string, and print as (nicer) IO
prettyPrePrint :: LambdaPreTerm -> String
prettyPrePrint (V x) = show x
prettyPrePrint (A m n) = "(" ++ prettyPrePrint m ++ " " ++ prettyPrePrint n ++ ")"
prettyPrePrint (L x m) =   "(\\" ++ show x ++ ". " ++ prettyPrePrint m ++ ")"

prettierPrePrint :: LambdaPreTerm -> IO ()
prettierPrePrint term =
  putStrLn $ prettyPrePrint term


-- print as string, and print as (nicer) IO
prettyPrint :: LambdaTerm -> String
prettyPrint (T m) = prettyPrePrint m

prettierPrint :: LambdaTerm -> IO ()
prettierPrint = putStrLn . prettyPrint