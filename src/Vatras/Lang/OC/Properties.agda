{-|
This module contains proofs of some basic properties of
option calculus.
-}
module Vatras.Lang.OC.Properties where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (∞)

open import Vatras.Framework.Definitions using (𝔽; 𝔸)
import Vatras.Framework.Variants as V
open import Vatras.Lang.All
open OC using (OC; _-<_>-; _❲_❳; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse; all-oc)

{-|
For any option calculus expression `e` we can derive a variant by including all options.
-}
⟦e⟧ₒtrue≡just : ∀ {F : 𝔽} {A : 𝔸} (e : OC F ∞ A) → ∃[ v ] ⟦ e ⟧ₒ (all-oc true) ≡ just v
⟦e⟧ₒtrue≡just (a -< cs >-) = a V.-< ⟦ cs ⟧ₒ-recurse (all-oc true) >- , refl
⟦e⟧ₒtrue≡just (f ❲ e ❳) = ⟦e⟧ₒtrue≡just e
