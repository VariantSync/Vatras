open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Lang.CCC.Util {Dimension : 𝔽} where

open import Size using (Size)
open import Data.List as List using (List; _∷_)
import Data.List.NonEmpty as List⁺

open import Vatras.Lang.CCC Dimension using (CCC; _-<_>-; _⟨_⟩)

-- Recursively, collect all dimensions used in a CCC expression:
dims : ∀ {i : Size} {A : 𝔸} → CCC i A → List Dimension
dims (_ -< es >-) = List.concatMap dims es
dims (D ⟨ es ⟩) = D ∷ List.concatMap dims (List⁺.toList es)
