module Lang.OC.Properties where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (∞)

open import Framework.Definitions using (𝔽; 𝔸)
import Framework.Variants as V
open import Lang.All
open OC using (OC; _-<_>-; _❲_❳; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse; all-oc)

⟦e⟧ₒtrue≡just : ∀ {F : 𝔽} {A : 𝔸} (e : OC F ∞ A) → ∃[ v ] ⟦ e ⟧ₒ (all-oc true) ≡ just v
⟦e⟧ₒtrue≡just (a -< cs >-) = a V.-< ⟦ cs ⟧ₒ-recurse (all-oc true) >- , refl
⟦e⟧ₒtrue≡just (f ❲ e ❳) = ⟦e⟧ₒtrue≡just e
