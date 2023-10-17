module Framework.V2.Annotation.Negatable where

open import Framework.V2.Annotation.Name using (Name)
open import Data.Bool using (Bool; true; false; not)

{-|
A logic that only knows variables or their negations.
TODO: Make this an instance of 𝔽.
-}
data Negatable {ℓ} (A : Set ℓ) : Set ℓ where
  if  : Name A → Negatable A
  ifn : Name A → Negatable A

eval : ∀ {ℓ} {A : Set ℓ} → Negatable A → (Name A → Bool) → Bool
eval (if  n) c = c n
eval (ifn n) c = not (c n)

mkConfig : ∀ {ℓ} {A : Set ℓ} → (Name A → Bool) → Negatable A → Bool
mkConfig c n = eval n c
