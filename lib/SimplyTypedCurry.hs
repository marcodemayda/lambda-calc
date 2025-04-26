{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module SimplyTypedCurry where

import PreTerms
import Untyped
import Basics


import Data.Foldable
import Data.List
import Data.Tuple



---BEGINNINGS-----------
-- Base types Ty, and arrow types To 

type Atom = Integer

data Type = Ty Atom | To Type Type
    deriving (Eq, Show)

typeAtoms :: [Atom]
typeAtoms = [1..]

-- types = map Ty typeAtoms ++ (map To (map Ty typeAtoms))

-- A context is a "set" of tuples asigning variables to a type.
type Context = [(Var, Type)]


contextVar :: Context -> [Var]
contextVar = map fst
contextDom :: Context -> [Var]
contextDom = contextVar

contextTypes :: Context -> [Type]
contextTypes = map snd
contextRan :: Context -> [Type]
contextRan = contextTypes

contextAdd :: Context -> (Var,Type) -> Context
contextAdd = undefined

-- domain contexts need to be (partial) functional w.r.t variables.
checkWellDefContext :: Context -> Bool
checkWellDefContext ga = map fst ga == nub (map fst ga)

-- type of a variable in a context.
typeOf :: Var -> Context -> Maybe Type
typeOf = lookup


-- THe list of variables in a context that have a of a given type
typedVars ::  Context -> Type  -> [Var]
typedVars g t
    | t `elem` contextRan g = [x | x <- contextDom g, (x,t) `elem` g]
    | otherwise = []


contextExtend :: Context -> (Var,Type) -> Maybe Context
contextExtend ga tup
    |checkWellDefContext (ga ++ [tup]) = Just $ ga ++ [tup]
    | otherwise = Nothing




------------ JUDGMENTS
type Judgment = (Context, (LambdaTerm, Type))



checkInferVAR :: Judgment -> Bool
checkInferVAR (ga, (la, t)) = any (\(x,y) -> (T (V x),y) == (la,t)) ga

checkInferABS :: Judgment -> Judgment -> Bool
checkInferABS (ga1, (la1,t1)) (ga2, (la2,t2)) = case la2 of
        T (L x m) -> case t2 of
                To si ta -> typeOf x ga1 == Just si
                            && t1 == ta
                            && ga2 == ga1 \\ [(x, si)]
                            && la1 == T m
                _ -> False
        _ -> False

checkInferAPP :: Judgment -> Judgment -> Judgment ->  Bool
checkInferAPP (ga1, (la1, t1)) (ga2, (la2,t2)) (ga3, (la3, t3)) =
    case t1 of
        To ta si -> ga1 == ga2 && ga2 == ga3
                    && la3 == T  (A (preTer la1) (preTer la2))
                    && t2 == si && t3 == ta
        _ -> False






----------- TYPABLE and CHECKING
--- this i prob out of my wheelhouse, but putting it in, maybe I'll get to it sometime.

-- Type check problem: decide if a judgment holds (i.e. is derivable, i.e., i think, there is a prooftree to it, whose leaves are all VAR, and each child respects ABS or APP)
checkTypeCheck :: Judgment -> Bool
checkTypeCheck (ga, (m,ta)) = undefined

checkTypeCheckAlt :: Judgment -> Bool
checkTypeCheckAlt = undefined

-- Type Typability/Reconstruction Problem: decide if for a given term, there exists a context and type Gamma,sigma, such that  Gamma M sigma type-checks
checkTypable :: LambdaTerm -> Bool
checkTypable m = checkTypeCheck (b, (m', Ty 1))
    where
        m' = T$ A (A (preTer combiK) (V (freshVar m))) (lambdaVec (freeVars m) (preTer m))
        b = [(freshVar m, Ty 1)]
--By pg 60 this suffices

typableConstruction  m = undefined

-- >>> T$ (map L [1,2,3])(V 4)
-- Variable not in scope: m

-- Type inhabitation/emptiness problem: given a Type, decide wether there is (closed) LambdaTerm such that Judment with the empty context holds for them.
checkInhabitable :: Type -> Bool
checkInhabitable = undefined






-----------------
