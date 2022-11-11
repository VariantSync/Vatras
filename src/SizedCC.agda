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

-- The size parameter is an upper bound of nesting depth.
-- In the constructors, j denotes an upper bound for the nesting depth of children.
-- Name it SCC for Sized Choice Calculus
data SCC (i : Size) (A : Set) : Set where
  Artifact : ∀ {j : Size< i}
    → A → List (SCC j A) → SCC i A
  _⟨_⟩ : ∀ {j : Size< i}
    → Dimension → List⁺ (SCC j A) → SCC i A

-- Any upper bound is fine but we are at least 1 deep.
leaf : ∀ {i : Size} → String → SCC (↑ i) String
leaf s = Artifact s []

-- Any upper bound is fine but we are at least 2 deep.
example1 : ∀ {i : Size} → SCC (↑ (↑ i)) String
example1 = "Ekko" ⟨ leaf "sleep"  ∷ leaf "zoom" ∷ [] ⟩

-- This is now proved to terminate by Agda.
map-scc : ∀ {i : Size} {A B : Set} → (f : A → B) → SCC i A → SCC i B
map-scc f (Artifact a es) = Artifact (f a) (mapl (map-scc f) es)
map-scc f (D ⟨ es ⟩) = D ⟨ mapl⁺ (map-scc f) es ⟩

-- Can we get back to CC without params?
CC : Set → Set
CC = SCC ∞ -- Usually, we do not know the bound so we just say infinite.

example2 : CC String
example2 = "Becca" ⟨ leaf "eatCarrot" ∷ leaf "sleep" ∷ [] ⟩ -- Wow this is nice! *-*

-- But what about the implicit bounds?
-- Termination checking fails. :(
-- Not unexpected though because by using ∞ everywhere we basically lost the depth constraint again.
{-# TERMINATING #-}
map-cc : ∀ {A B : Set} → (f : A → B) → CC A → CC B
map-cc f (Artifact a es) = Artifact (f a) (mapl (map-cc f) es)
map-cc f (D ⟨ es ⟩) = D ⟨ mapl⁺ (map-cc f) es ⟩
