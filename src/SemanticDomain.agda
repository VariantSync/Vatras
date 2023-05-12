module SemanticDomain where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin; inject₁)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-l)
open import Data.String using (String; _++_; intersperse)
open import Function using (_∘_)

open import Data.Multiset using (Multiset; Index; nonempty)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; isYes)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Variant (A : Set) : Set where
  Artifactᵥ : A → List (Variant A) → Variant A

VSet : ℕ → Set → Set
VSet size-1 A = Multiset (Fin (suc size-1)) (Variant A)
-- record VSet (A : Set) : Set where
--   constructor _/_
--   field
--     size-1 : ℕ
--     pick : Multiset (Fin (suc size-1)) (Variant A)
-- open VSet public

forget-last : ∀ {n : ℕ} {A : Set} → VSet (suc n) A → VSet n A
forget-last set x = set (inject₁ x)

leaf : ∀ {A : Set} → A → Variant A
leaf a = Artifactᵥ a []

leaves : ∀ {A : Set} → List A → List (Variant A)
leaves as = map leaf as

-- We did not equip variants with bounds yet so we just assume the following functions to terminate.

-- ## Equality

root-equality : ∀ {A : Set} {a b : A} {as bs : List (Variant A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → a ≡ b
root-equality refl = refl

subtree-equality : ∀ {A : Set} {a b : A} {as bs : List (Variant A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → as ≡ bs
subtree-equality refl = refl

{-# TERMINATING #-}
≡-dec : ∀ {A : Set} → DecidableEquality A → DecidableEquality (Variant A)
≡-dec ≡-dec-A (Artifactᵥ a as) (Artifactᵥ b bs) with ≡-dec-A a b | ≡-dec-l (≡-dec ≡-dec-A) as bs
... | yes a≡b | yes as≡bs = yes (Eq.cong₂ Artifactᵥ a≡b as≡bs)
... | yes a≡b | no ¬as≡bs = no (¬as≡bs ∘ subtree-equality)
... | no ¬a≡b | _         = no (¬a≡b   ∘ root-equality)

equals : ∀ {A : Set} → DecidableEquality A → Variant A → Variant A → Bool
equals ≡-dec-A V W = isYes (≡-dec ≡-dec-A V W)

module Examples where
  open import Data.Fin using (Fin; suc; zero)
  open import Data.Nat using (ℕ)

  vset-example : VSet 2 ℕ
  vset-example zero = leaf 1
  vset-example (suc zero) = leaf 2
  vset-example (suc (suc zero)) = leaf 2 -- multiset possible because injectivity is not required

--## Show

{-# TERMINATING #-}
show-variant : ∀ {A : Set} → (A → String) → Variant A → String
show-variant s (Artifactᵥ a []) = s a
show-variant s (Artifactᵥ a es@(_ ∷ _)) = s a ++ "-<" ++ (intersperse ", " (map (show-variant s) es)) ++ ">-"

