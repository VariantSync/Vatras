module Vatras.Framework.Annotation.Negatable where

open import Vatras.Framework.Definitions using (𝔽)
open import Data.Bool using (Bool; true; false; not)

{-|
An annotation language that adds negations to an existing
annotation language.
-}
data Negatable (F : 𝔽) : 𝔽 where
  if  : F → Negatable F
  ifn : F → Negatable F

{-|
Semantics of Negatable.
Given a boolean configuration for the underlying
annotation type, Negatable may flip the result if
the ifn is chosen.
This could potentially be generalized for other
interpretations of negations in the result type.
-}
eval : ∀ {F : 𝔽} → Negatable F → (F → Bool) → Bool
eval (if  n) c =      c n
eval (ifn n) c = not (c n)

{-|
Converse to 'eval':
Given a boolean configuration for the underlying
annotation type F, creates a configuration for Negatable.
-}
mkConfig : ∀ {F : 𝔽} → (F → Bool) → Negatable F → Bool
mkConfig c n = eval n c
