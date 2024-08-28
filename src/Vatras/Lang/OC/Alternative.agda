{-|
This module proves that option calculus cannot encode alternatives,
at the example of natural numbers as the atom set.
The proof is restricted to variants with alternatives at their root.
-}
module Vatras.Lang.OC.Alternative where

open import Data.List using (List; []; _∷_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc; _≟_; ℕ)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (Sublist; _∷_; _∷ʳ_)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (∞)

open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
open import Vatras.Framework.Variants using (Rose; rose-leaf; _-<_>-; children-equality)
open import Vatras.Lang.All
open OC using (WFOC; Root; all-oc)
open import Vatras.Lang.OC.Subtree using (Subtree; subtrees; subtreeₒ-recurse)

A : 𝔸
A = ℕ , _≟_

cannotEncodeAlternative : ∀ {F : 𝔽}
  → (e : WFOC F ∞ A)
  → (∃[ c ] zero -< rose-leaf      zero  ∷ [] >- ≡ OC.⟦ e ⟧ c)
  → (∃[ c ] zero -< rose-leaf (suc zero) ∷ [] >- ≡ OC.⟦ e ⟧ c)
  → (zero -< [] >- ≡ OC.⟦ e ⟧ (all-oc false))
  → Subtree (zero -< rose-leaf zero ∷ rose-leaf (suc zero) ∷ [] >-) (OC.⟦ e ⟧ (all-oc true))
  ⊎ Subtree (zero -< rose-leaf (suc zero) ∷ rose-leaf zero ∷ [] >-) (OC.⟦ e ⟧ (all-oc true))
cannotEncodeAlternative e@(Root zero cs) p₁ p₂ p₃ = Sum.map subtrees subtrees (mergeSubtrees' (sublist p₁) (sublist p₂))
  where
  sublist : ∀ {a : atoms A} {v : Rose ∞ A} → (∃[ c ] a -< v ∷ [] >- ≡ OC.⟦ e ⟧ c) → Sublist Subtree (v ∷ []) (OC.⟦ cs ⟧ₒ-recurse (all-oc true))
  sublist (c₁ , p₁) =
    Eq.subst
      (λ cs' → Sublist Subtree cs' (OC.⟦ cs ⟧ₒ-recurse (all-oc true)))
      (children-equality (Eq.sym p₁))
      (subtreeₒ-recurse cs c₁ (all-oc true) (λ f p → refl))

  mergeSubtrees' : ∀ {cs : List (Rose ∞ A)}
    → Sublist Subtree (rose-leaf zero ∷ []) cs
    → Sublist Subtree (rose-leaf (suc zero) ∷ []) cs
    → Sublist Subtree (rose-leaf zero ∷ rose-leaf (suc zero) ∷ []) cs
    ⊎ Sublist Subtree (rose-leaf (suc zero) ∷ rose-leaf zero ∷ []) cs
  mergeSubtrees' (a ∷ʳ as₁) (.a ∷ʳ as₂) = Sum.map (a ∷ʳ_) (a ∷ʳ_) (mergeSubtrees' as₁ as₂)
  mergeSubtrees' (a₁ ∷ʳ as₁) (p₂ ∷ as₂) = inj₂ (p₂ ∷ as₁)
  mergeSubtrees' (p₁ ∷ as₁) (a₂ ∷ʳ as₂) = inj₁ (p₁ ∷ as₂)
  mergeSubtrees' (subtrees v ∷ as₁) (() ∷ as₂)
