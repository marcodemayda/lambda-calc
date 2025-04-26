{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module SimplyTypedCurry where

import PreTerms
import Untyped

import Data.Foldable
import Data.List (nub)
import Data.Tuple



---BEGINNINGS-----------
-- Base types Ty, and arrow types To 
data Type = Ty Int | To Type Type
    deriving (Eq, Show)

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


checkWellDefContext :: Context -> Bool
checkWellDefContext ga = map fst ga == nub (map fst ga)

typeOf :: Var -> Context -> Maybe Type
typeOf = lookup



------------ JUDGMENTS
type Judgment = (Context, (LambdaTerm, Type))



checkInferVAR :: Judgment -> Bool
checkInferVAR (ga, (la, t)) = any (\(x,y) -> (T(V x),y) == (la,t)) ga


checkInferABS :: Judgment -> Judgment -> Bool
checkInferABS (ga1, (la1,t1)) (ga2, (la2,t2)) = case t2 of
    To si ta ->    True -- missing "ga1 contains (x, si) for some variable x, and ga2 == ga1-(x,si)"
                && t1 == si && t2 == ta
                && la2 == T (L 1 (preTer la1))
    _ -> False
    

checkInferAPP :: Judgment -> Judgment -> Judgment ->  Bool
checkInferAPP (ga1, (la1, t1)) (ga2, (la2,t2)) (ga3, (la3, t3)) =
    case t1 of
        To ta si -> ga1 == ga2 && ga2 == ga3
                    && la3 == T  (A (preTer la1) (preTer la2))
                    && t2 == si && t3 == ta
        _ -> False