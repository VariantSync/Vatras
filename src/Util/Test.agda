module Util.Test where

open import Data.String using (String)
open import Data.Maybe using (Maybe)
open import Data.List using (List)

Error : Set
Error = String

record TestCase (A B : Set) : Set where
  field
    name : String
    input : A
    expectedOutput : B

record Test (A B : Set) : Set where
  field
    name : String
    testcases : List (TestCase A B)
    isExpected : (actualResult : B) → (expectedResult : B) → Maybe Error

--runTest : ∀ {A B : Set} → Test A B → List Error
--runTest t = 


