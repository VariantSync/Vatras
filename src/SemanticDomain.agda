{-# OPTIONS --sized-types #-}

module SemanticDomain where

open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; _++_; intersperse)
--open import Size using (Size; Size<_)

data Variant
  --(i : Size)
  (A : Set) : Set
  where
  Artifactᵥ : --{j : Size< i} →
    A → List (Variant A) → Variant A

leaf : ∀ {A : Set} → A → Variant A
leaf a = Artifactᵥ a []

leaves : ∀ {A : Set} → List A → List (Variant A)
leaves as = map leaf as

-- We did not equip variants with bounds yet so we just assume this terminates.
{-# TERMINATING #-}
showVariant : Variant String → String
showVariant (Artifactᵥ a []) = a
showVariant (Artifactᵥ a es@(_ ∷ _)) = a ++ "-<" ++ (intersperse ", " (map showVariant es)) ++ ">-"
