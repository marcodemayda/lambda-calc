{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module SimplyTypedCurry where

import PreTerms
import Untyped
import Basics



import Data.List 




---BEGINNINGS-----------
-- Base types Ty, and arrow types To 

type Atom = Integer

data ArType = Ty Atom | To ArType ArType
    deriving (Eq, Show)

typeAtoms :: [Atom]
typeAtoms = [1..]

-- types = map Ty typeAtoms ++ (map To (map Ty typeAtoms))

-- A context is a "set" of tuples asigning variables to a type.
type Context = [(Var, ArType)]

atomsOf :: ArType -> [Atom]
atomsOf (Ty x) = [x]
atomsOf (x `To` y) = atomsOf x ++ atomsOf y

contextVar :: Context -> [Var]
contextVar = map fst
contextDom :: Context -> [Var]
contextDom = contextVar

contextTypes :: Context -> [ArType]
contextTypes = map snd
contextRan :: Context -> [ArType]
contextRan = contextTypes

contextAdd :: Context -> (Var,ArType) -> Context
contextAdd = undefined

-- domain contexts need to be (partial) functional w.r.t variables.
checkWellDefContext :: Context -> Bool
checkWellDefContext ga = map fst ga == nub (map fst ga)

-- type of a variable in a context.
typeOf :: Var -> Context -> Maybe ArType
typeOf = lookup


-- THe list of variables in a context that have a of a given type
typedVars ::  Context -> ArType  -> [Var]
typedVars g t
    | t `elem` contextRan g = [x | x <- contextDom g, (x,t) `elem` g]
    | otherwise = []



contextExtend :: Context -> (Var,ArType) -> Maybe Context
contextExtend ga tup
    |checkWellDefContext (ga ++ [tup]) = Just $ ga ++ [tup]
    | otherwise = Nothing



------------ JUDGMENTS --------------
type JudgmentCu = (Context, (LambdaTerm, ArType))



checkInferVAR :: JudgmentCu -> Bool
checkInferVAR (ga, (la, t)) = any (\(x,y) -> (T (V x),y) == (la,t)) ga

checkInferABS :: JudgmentCu -> JudgmentCu -> Bool
checkInferABS (ga1, (la1,t1)) (ga2, (la2,t2)) = case la2 of
        T (L x m) -> case t2 of
                si `To` ta -> typeOf x ga1 == Just si
                            && t1 == ta
                            && ga2 == ga1 \\ [(x, si)]
                            && la1 == T m
                _ -> False
        _ -> False

checkInferAPP :: JudgmentCu -> JudgmentCu -> JudgmentCu ->  Bool
checkInferAPP (ga1, (la1, t1)) (ga2, (la2,t2)) (ga3, (la3, t3)) =
    case t1 of
        ta `To` si -> ga1 == ga2 && ga2 == ga3
                    && la3 == T  (A (preTer la1) (preTer la2))
                    && t2 == si && t3 == ta
        _ -> False