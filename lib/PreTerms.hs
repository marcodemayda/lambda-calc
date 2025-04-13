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

prettyPrePrint2 :: LambdaPreTerm -> String
prettyPrePrint2 (V x) = show x
prettyPrePrint2 (A m n) = "(" ++ prettyPrePrint m ++ " " ++ prettyPrePrint n ++ ")"
prettyPrePrint2 (L x m) =   "(\x03bb" ++ show x ++ ". " ++ prettyPrePrint m ++ ")"

prettierPrePrint :: LambdaPreTerm -> IO ()
prettierPrePrint term = do
  hSetEncoding stdout utf8
  putStrLn $ prettyPrePrint2 term

-- prettierPrePrint (L 3 (V 3))


-- lists free variables in a Pre-term
freePreVars :: LambdaPreTerm -> [Var]
freePreVars (V x) = [x]
freePreVars (L x m) = [y | y <- freePreVars m,  y /= x]
freePreVars (A m n) = nub $ freePreVars m ++ freePreVars n


-- check if x is a freevariable of Pre-term n
checkFreePreVar :: Var -> LambdaPreTerm -> Bool
checkFreePreVar x n = x `elem` freePreVars n


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


alphaConvTot:: LambdaPreTerm -> Var -> LambdaPreTerm
alphaConvTot (V x) _ = V x
alphaConvTot (L x m) y
    | checkFreePreVar y m = L x m
    | otherwise = L y (substPreTot m x (V y))
alphaConvTot (A m n) _ = A m n


alphaEq :: LambdaPreTerm -> LambdaPreTerm -> Bool
alphaEq (V x) (V y) = x == y
alphaEq (A m1 n1) (A m2 n2) = alphaEq m1 m2 && alphaEq n1 n2
alphaEq (L x m) (L y n)
    | x == y = alphaEq m n
    | alphaConv (L x m) y == Just (L y n) = True
    | otherwise =  False
alphaEq _ _ = False



---------- LAMBDA TERMS ----------
newtype LambdaTerm = T LambdaPreTerm
    deriving (Show)

instance Eq LambdaTerm where
    T m == T n = alphaEq m n


-- data LambdaFull =  X Var | X LambdaFull LambdaFull | X LambdaFull LambdaFull


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



-- again read "Term with Variable substituted for Term"
substTerm :: LambdaTerm -> Var -> LambdaTerm -> Maybe LambdaTerm
substTerm (T m) x (T n) = do
    t <- substPreTerm m x n
    return $ T t

prettySub :: LambdaTerm -> Var -> LambdaTerm -> IO ()
prettySub (T m) x (T n) = prettierPrePrint $ fromJust $ substPreTerm m x n


---------- Total SubstitutionS ----------
substPreTot :: LambdaPreTerm -> Var -> LambdaPreTerm -> LambdaPreTerm
substPreTot (V y) x n
    | y /= x    = V y
    | otherwise = n
substPreTot (A p q) x n =  A (substPreTot p x n) (substPreTot q x n)
substPreTot (L y p) x n
    | isJust$ substPreTerm (L y p) x n =  L y (substPreTot p x n)
    | otherwise = substPreTot (alphaConvTot (L y p) (head$ ([1..] \\ freePreVars (L y p)) \\ [x])) x n


substTermTot :: LambdaTerm -> Var -> LambdaTerm -> LambdaTerm
substTermTot (T m) x (T n)= T$ substPreTot m x n

alphaTotConv :: LambdaPreTerm -> Var -> LambdaPreTerm
alphaTotConv (V x) _ = V x
alphaTotConv (L x m) y
    | checkFreePreVar y m = L x m
    | otherwise = L y (substPreTot m x (V y))
alphaTotConv (A m n) _ = A m n


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



-- change an entire sub-term. read "Term with sub-term p substituted for Term q".
-- substForPreTerm :: LambdaPreTerm -> LambdaPreTerm -> LambdaPreTerm -> LambdaTerm
-- substForPreTerm (V x) p q
--     | (V x) == p = q 
--     | otherwise = (V x)


-- substForTerm (A m n) p q 
--     | p `elem` substPreTerm (A m n) = (A m n) 
--     | otherwise = (A m n)

-- substForTerm (L x m) p q 
--     | p `elem` substPreTerm (L x m) = undefined
--     | otherwise = (A m n)


    -- | T x `elem` subPreTerms m = case 
    -- | otherwise = m
