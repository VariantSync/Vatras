module SemanticDomain where

open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; _++_; intersperse)

data Variant (A : Set) : Set where
  Artifactᵥ : A → List (Variant A) → Variant A

-- We did not equip variants with bounds yet so we just assume this terminates.
{-# TERMINATING #-}
showVariant : Variant String → String
showVariant (Artifactᵥ a []) = a
showVariant (Artifactᵥ a es@(_ ∷ _)) = a ++ "-<" ++ (intersperse ", " (map showVariant es)) ++ ">-"
