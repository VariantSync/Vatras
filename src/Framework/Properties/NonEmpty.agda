{-|
This module provides definitions to say that
the semantics of a variability language are non-empty.
-}
module Framework.Properties.NonEmpty where

open import Framework.VariabilityLanguage using (VariabilityLanguage; Expression; Config; Semantics)
open import Data.EqIndexedSet

{-|
A variability language is not empty if there exists at least one configuration for each expression.
-}
NonEmpty : ∀ {V} (L : VariabilityLanguage V) → Set₁
NonEmpty L = ∀ {A} → Expression L A → Config L

{-|
A sanity check that our definition of NonEmpty
indeed ensures that the semantics of the language
can never be an empty indexed set.
-}
sane : ∀ {V} {L : VariabilityLanguage V}
  → NonEmpty L
    -----------------------------------------------------
  → ∀ {A} (e : Expression L A) → nonempty (Semantics L e)
sane give-me-a-config e = give-me-a-config e
