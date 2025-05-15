
module Parser where

import Text.Parsec
import Text.Parsec.String (Parser)

import PreTerms
import Untyped




{-
idea is:

turn V 1 into x, (gotta  make a mapping of Int to available lowercase letter for multiples)

turn A m n into M N
turn L x m into \x m and λx. M

Turn \x1. ...\xn. to \x1...xn., and likewise
Cancel outermost parenthesis
Turn MNP to ...?(double check convention)
-}



{-

data Form = P Integer | Neg Form | Dia Form | Conj Form Form | Imp Form Form
  deriving (Eq,Show)

pForm :: Parsec String () Form
pForm = spaces *> pImp <* spaces
  where
    --implication
    pImp = chainr1 pConj (spaces *> string "->" *> spaces *> return Imp)
    -- a conjunction is a sequence of atoms connected by '&':
    pConj = chainl1 pAtom (spaces *> char '&' *> spaces *> return Conj)
    -- an atom is a variable or a negation or a conjunction in parentheses (and additions):
    pAtom = spaces *> (pVar <|> pNeg <|> pDia <|> pParens) <* spaces
    -- a variable is 'p' followed by some digits:
    pVar  = char 'p' >> P . read <$> many1 digit
    -- a negation is '!' followed by an atom:
    pNeg  = char '!' *> spaces *> (Neg <$> pAtom)
    --diamonds
    pDia  = string "<>" *> spaces *> (Dia <$> pAtom)
    --parentheses
    pParens = char '(' *> spaces *> pForm <* spaces <* char ')'

parseForm :: String -> Either ParseError Form
parseForm = parse (spaces *> pForm <* eof) "input"

-}