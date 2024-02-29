{-# OPTIONS --sized-types #-}
module Lang.Choices where

open import Data.Fin using (Fin)
open import Data.List as List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ; zero)
open import Data.Vec as Vec using (Vec)
open import Size using (Size; ↑_)
open import Util.List using (find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using (_-<_>-) renaming (Syntax to Artifact)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (refl)

data Variant (A : Set) : Set where
  artifact : A → List (Variant A) → Variant A

Artifact∈ₛVariant : Artifact ∈ₛ Variant
Artifact∈ₛVariant .cons (a -< cs >-) = artifact a cs
Artifact∈ₛVariant .snoc (artifact a cs) = just (a -< cs >-)
Artifact∈ₛVariant .id-l (a -< cs >-) = refl
