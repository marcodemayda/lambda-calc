{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
module TypeabilityChecking where



import PreTerms
import Untyped
import Basics
import SimplyTypedCurry

-- this might be out of my wheelhouse tbh; depending how far i wanna go with it.


------------- THE MAIN PROBLEMS -----------------------
-- Type check problem: decide if a judgment holds (i.e. is derivable, i.e., i think, there is a prooftree to it, whose leaves are all VAR, and each child respects ABS or APP)
checkTypeCheck :: JudgmentCu -> Bool
checkTypeCheck (ga, (m,ta)) = undefined

checkSimplyTypeCheck :: JudgmentCu -> Bool
checkSimplyTypeCheck = undefined

-- Type Typability/Reconstruction Problem: decide if for a given term, there exists a context and type Gamma,sigma, such that  Gamma M sigma type-checks
checkSimplyTypable :: LambdaTerm -> Bool
checkSimplyTypable m = checkSimplyTypeCheck (b, (m', Ty 1))
    where
        m' = T$ A (A (preTer combiK) (V (freshVar m))) (lambdaVec (freeVars m) (preTer m))
        b = [(freshVar m, Ty 1)]
--By pg 60 this suffices for simply typed systems

typableConstruction  m = undefined

-- >>> T$ (map L [1,2,3])(V 4)
-- Variable not in scope: m

-- Type inhabitation/emptiness problem: given a Type, decide wether there is (closed) LambdaTerm such that Judment with the empty context holds for them.
checkInhabitable :: ArType -> Bool
checkInhabitable = undefined




----------------- WORKINGS ---------------------

auxiliarVars :: LambdaPreTerm -> ArType -> [Var]
auxiliarVars (V x) (Ty p)
    | x == p = [x]
    | otherwise = []
auxiliarVars (A m n) (Ty p) = auxiliarVars m (Ty p) ++ auxiliarVars n (Ty p)
auxiliarVars (L _ m) (Ty p) = auxiliarVars m (Ty p)
auxiliarVars (V x) (ta `To` si)  = undefined
auxiliarVars (A m n) (ta `To` si) = undefined
auxiliarVars (L _ m) (ta `To` si) = undefined




-- NOTE: both are unfinished; naive w.r.t to variables in the application case. Also need to make the renaming so that each Em is unique for a term m.
equationSysteM :: LambdaTerm -> [ArType]
equationSysteM (T (V _)) = []
equationSysteM (T (A p q)) = equationSysteM (T p) ++ equationSysteM (T q) ++ [typeSysteM (T q) `To` typeSysteM (T (A p q))]
equationSysteM (T (L x m)) = equationSysteM $ T (substPreTot m x (V (freshPreVar m)))

typeSysteM :: LambdaTerm -> ArType
typeSysteM (T (V x)) = Ty x
typeSysteM (T (A m n)) = Ty (freshPreVar (A m n))
typeSysteM (T (L x m)) = Ty (freshPreVar m) `To` typeSysteM (T $ substPreTot m x (V (freshPreVar m)))


