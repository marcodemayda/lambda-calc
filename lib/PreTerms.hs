{-# LANGUAGE InstanceSigs #-}
module PreTerms where


import System.IO (stdout, hSetEncoding, utf8)
import Data.Maybe
import Data.List


---------- PRE TERMS ----------
type Var = Integer

variables :: [Var]
variables = [1..]


data LambdaPreTerm =  V Var | A LambdaPreTerm LambdaPreTerm  | L Var LambdaPreTerm
    deriving (Show, Eq)

-- print Pre-term as string, and print as (nicer) IO
prettyPrePrint :: LambdaPreTerm -> String
prettyPrePrint (V x) = show x
prettyPrePrint (A m n) = "(" ++ prettyPrePrint m ++ " " ++ prettyPrePrint n ++ ")"
prettyPrePrint (L x m) =   "(\\" ++ show x ++ ". " ++ prettyPrePrint m ++ ")"

prettierPrePrint :: LambdaPreTerm -> IO ()
prettierPrePrint term = do
  hSetEncoding stdout utf8
  putStrLn $ prettyPrePrint term


-- lists free variables in a Pre-term
freePreVars :: LambdaPreTerm -> [Var]
freePreVars (V x) = [x]
freePreVars (L x m) = [y | y <- freePreVars m,  y /= x]
freePreVars (A m n) = nub $ freePreVars m ++ freePreVars n

-- check if x is a freevariable of Pre-term n
checkFreePreVar :: Var -> LambdaPreTerm -> Bool
checkFreePreVar x n = x `elem` freePreVars n


variablesPreOf :: LambdaPreTerm -> [Var]
variablesPreOf (V x) = [x]
variablesPreOf (A m n) = nub $ variablesPreOf m ++ variablesPreOf n
variablesPreOf (L _ m) = variablesPreOf m


freshPreVar :: LambdaPreTerm -> Var
freshPreVar m = head $ variables \\ variablesPreOf m



-- a vector of \x\y\z... M
lambdaVec :: [Var] -> LambdaPreTerm -> LambdaPreTerm
lambdaVec xs m = foldr L m xs


-- substitution for Pre-terms, read "Pre-term with Var substituted for Pre-term"
substPreTerm :: LambdaPreTerm -> Var -> LambdaPreTerm -> Maybe LambdaPreTerm
substPreTerm (V y) x n
    | y /= x    = Just (V y)
    | otherwise = Just n
substPreTerm (A p q) x n = do
    p' <- substPreTerm p x n
    q' <- substPreTerm q x n
    return $ A p' q'
substPreTerm (L y p) x n
    | checkFreePreVar x (L y p) && checkFreePreVar y n = Nothing -- Variable capture (see definition 1.2.4)
    | x /= y && not (checkFreePreVar y n && checkFreePreVar x p) = do
        p' <- substPreTerm p x n
        return $ L y p'
    | otherwise = Just $ L y p


prettyPreSub :: LambdaPreTerm -> Var -> LambdaPreTerm -> IO ()
prettyPreSub m x n = prettierPrePrint $ fromJust $ substPreTerm m x n

-- alpha conevrt Term with Variable
alphaConv :: LambdaPreTerm -> Var -> Maybe LambdaPreTerm
alphaConv (V _) _ = Nothing
alphaConv (L x m) y
    | checkFreePreVar y m = Nothing
    | otherwise = do
        m' <- substPreTerm m x (V y)
        return$ L y m'
alphaConv (A _ _) _ = Nothing


alphaConvTot:: LambdaPreTerm -> LambdaPreTerm
alphaConvTot (L x m) = case alphaConv (L x m) (head $ freePreVars (L x m)) of 
    Just n -> n
    Nothing -> error "stuff"
alphaConvTot m = m


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


-- print as string, and print as (nicer) IO
prettyPrint :: LambdaTerm -> String
prettyPrint (T m) = prettyPrePrint m

prettierPrint :: LambdaTerm -> IO ()
prettierPrint = putStrLn . prettyPrint

-- lists free variables in a Term
freeVars :: LambdaTerm -> [Var]
freeVars (T m)= freePreVars m

-- check if x is a freevariable of Term n
checkFreeVar :: Var -> LambdaTerm -> Bool
checkFreeVar x (T m) = x `elem` freePreVars m


variablesOf :: LambdaTerm -> [Var]
variablesOf (T (V x)) = [x]
variablesOf (T (A m n)) = nub $ variablesPreOf m ++ variablesPreOf n
variablesOf (T (L _ m)) = variablesPreOf m


freshVar :: LambdaTerm -> Var
freshVar m = head $ variables \\ variablesOf m


-- again read "Term with Var substituted for Term"
substTerm :: LambdaTerm -> Var -> LambdaTerm -> Maybe LambdaTerm
substTerm (T m) x (T n) = do
    t <- substPreTerm m x n
    return $ T t

prettySub :: LambdaTerm -> Var -> LambdaTerm -> IO ()
prettySub (T m) x (T n) = prettierPrePrint $ fromJust $ substPreTerm m x n



---------- MORE FUNCTIONS ----------

checkCombinator :: LambdaTerm -> Bool
checkCombinator (T m) = null (freePreVars m)



mapPreTerm :: (LambdaPreTerm -> LambdaPreTerm) -> LambdaPreTerm -> LambdaPreTerm
mapPreTerm f (V x) = f (V x)
mapPreTerm f (A m n) = f$ A (mapPreTerm f m) (mapPreTerm f n)
mapPreTerm f (L x m) = f$ L x (mapPreTerm f m)


mapTerm :: (LambdaPreTerm -> LambdaPreTerm) -> LambdaTerm -> LambdaTerm
mapTerm f (T m) = T$ mapPreTerm f m


subPreTerms :: LambdaPreTerm -> [LambdaPreTerm]
subPreTerms (V x) = [V x]
subPreTerms (A m n) = A m n : subPreTerms m ++  subPreTerms n
subPreTerms (L x m) = L x m : subPreTerms m


subTerms :: LambdaTerm -> [LambdaTerm]
subTerms (T m) = map T (subPreTerms m)

preTer :: LambdaTerm -> LambdaPreTerm
preTer (T m) = m


------------- TOTAL FUNCTIONS -----------------
--------(of functions that aren't already)--------
-- NOTE: This might still need some work, it functions in "sane" cases, but i'm not sure it works generally
--potential problems: multiple instances of a sub-term;  Update: should be ok so long as it is fed a term that is unqiely identified, such as innermostRedex or the like, which is what I use it for anyways.
-- New Problem: i should account for variable capture with alpha-conversion...

-- change an entire sub-term. read "preTerm M with sub-term p substituted for preTerm q".

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
    | A p r `elem` subPreTerms k        = do L x <$> substForPreTerm k (A p r) q
    | otherwise                         = Nothing


substForPreTerm (A j k) (L y r) q
    | L y r `elem` subPreTerms j        =
        do
            j' <- substForPreTerm j (L y r) q
            return $ A j' k
    | L y r `elem` subPreTerms k        =
        do
            k' <- substForPreTerm k (L y r) q
            return $ A j k'
    | otherwise                         = Nothing
substForPreTerm (L x s) (L y r) q
    | L x s == L y r                    = Just q
    | L y r `elem` subPreTerms (L x s)  = L x <$> substForPreTerm s (L y r) q
    | otherwise                         = Nothing



substForPreTermTot :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm
substForPreTermTot m p q = case substForPreTerm m p q of
    Just m' -> m'
    Nothing 
        | p `elem` subPreTerms m -> case p of
        L x n -> substForPreTermTot m (alphaConvTot (L x n)) q
        _ -> m
        | otherwise -> error "second arguments needs to be a sub(pre)term of first"
