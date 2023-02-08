module SemanticDomain where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-l)
open import Data.String using (String; _++_; intersperse)
open import Function using (_∘_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; isYes)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Variant (A : Set) : Set where
  Artifactᵥ : A → List (Variant A) → Variant A

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

-- ## Show

{-# TERMINATING #-}
show-variant : ∀ {A : Set} → (A → String) → Variant A → String
show-variant s (Artifactᵥ a []) = s a
show-variant s (Artifactᵥ a es@(_ ∷ _)) = s a ++ "-<" ++ (intersperse ", " (map (show-variant s) es)) ++ ">-"


