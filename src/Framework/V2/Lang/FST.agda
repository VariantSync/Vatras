module Framework.V2.Lang.FST where

open import Data.List using (List) renaming (_∷_ to _．_)

open import Framework.V2.Annotation.Name using (Name)

record FeaturePath (N : Set) (S : Set) : Set where
  constructor _∷_
  field
    name : Name N
    path : List S
