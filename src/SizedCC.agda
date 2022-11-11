{-# OPTIONS --sized-types #-}

module SizedCC where

open import Size
open import Data.List.Base
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty.Base
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.String using (String)

Dimension : Set
Dimension = String

data CC (A : Set) : Size → Set where
  Artifact : ∀ {i : Size}
    → A → List (CC A i) → CC A (↑ i)
  _⟨_⟩ : ∀ {i : Size}
    → Dimension → List⁺ (CC A i) → CC A (↑ i)

leaf :  String → CC String ∞
leaf s = Artifact s []

example1 : CC String (↑ ∞)
example1 = "Ekko" ⟨ leaf "sleep"  ∷ leaf "zoom" ∷ [] ⟩

-- This is now proved to terminate by Agda.
map-cc : ∀ {i : Size} {A B : Set} → (f : A → B) → CC A i → CC B i
map-cc f (Artifact a es) = Artifact (f a) (mapl (map-cc f) es)
map-cc f (D ⟨ es ⟩) = D ⟨ mapl⁺ (map-cc f) es ⟩
