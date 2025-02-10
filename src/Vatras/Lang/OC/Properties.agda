{-|
This module contains proofs of some basic properties of
option calculus.
-}
open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Lang.OC.Properties (F : 𝔽) where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (∞)

import Vatras.Framework.Variants as V
open import Vatras.Lang.OC F using (OC; _-<_>-; _❲_❳; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse; all-oc)

{-|
For any option calculus expression `e` we can derive a variant by including all options.
-}
⟦e⟧ₒtrue≡just : ∀ {A : 𝔸} (e : OC ∞ A) → ∃[ v ] ⟦ e ⟧ₒ (all-oc true) ≡ just v
⟦e⟧ₒtrue≡just (a -< cs >-) = a V.-< ⟦ cs ⟧ₒ-recurse (all-oc true) >- , refl
⟦e⟧ₒtrue≡just (f ❲ e ❳) = ⟦e⟧ₒtrue≡just e
