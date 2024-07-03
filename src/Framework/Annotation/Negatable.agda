module Framework.Annotation.Negatable where

open import Framework.Definitions using (𝔽)
open import Data.Bool using (Bool; true; false; not)

{-|
An annotation language that adds negations to an existing
annotation language.
-}
data Negatable (F : 𝔽) : 𝔽 where
  if  : F → Negatable F
  ifn : F → Negatable F

eval : ∀ {F : 𝔽} → Negatable F → (F → Bool) → Bool
eval (if  n) c = c n
eval (ifn n) c = not (c n)

mkConfig : ∀ {F : 𝔽} → (F → Bool) → Negatable F → Bool
mkConfig c n = eval n c
