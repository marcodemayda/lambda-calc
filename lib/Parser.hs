
module Parser where

import Text.Parsec
import Text.Parsec.String (Parser)

import PreTerms
import Untyped




{-
idea is


turn "\x. m" into (L x (m))
turn "\x m" into  L x m
turn "(m n)" into  (A m n)
turn "x" that is not preceded by "\" into T


then 
turn "m n r" into "((m n) r)"
turn "\xy m" into "\x(\y m)"
turn "\x.y. m" into "\xy. (m)"

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