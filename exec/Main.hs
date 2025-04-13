module Main where

import PreTerms
import Untyped
 
import Parser


main :: IO ( )
main = putStrLn "Hello, no menu yet, sorry!"

  -- putStrLn $ "Ok" ++ name ++ "!"
  -- putStrLn "How old are you?"
  -- formula <- getLine
  -- case readMaybe ageInput of
  --       Just age | age >= 0 && age <= 111 -> do
  --           let earlyBirthYear = (2025 :: Int) - age
  --           let lateBirthYear = earlyBirthYear - 1
  --           putStrLn $ "Ah, so you were born in " ++ show lateBirthYear ++ " or " ++ show earlyBirthYear ++ "."
  --       _ -> putStrLn "Sorry, that is not a number."



{-
We can run this program with the commands:


stack build
stack exec myprogram
-}