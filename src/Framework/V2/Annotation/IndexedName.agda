module Framework.V2.Annotation.IndexedName where

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to show-ℕ)
open import Data.String using (String; _++_)

open import Framework.V2.Annotation.Name using (Name)

record IndexedName {ℓ} (N : Set ℓ) : Set ℓ where
  constructor _∙_
  field
    dim : Name N
    index : ℕ

show-IndexedName : ∀ {ℓ} {N : Set ℓ} → (N → String) → IndexedName N → String
show-IndexedName show-name (D ∙ i) = show-name D ++ "∙" ++ show-ℕ i
