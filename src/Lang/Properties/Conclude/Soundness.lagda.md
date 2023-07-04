# Theorems to Prove Soundness


```agda
{-# OPTIONS --sized-types #-}

module Lang.Properties.Conclude.Soundness where

open import Data.Product using (_,_)

open import Function using (_∘_; Surjective; Congruent)
open import Size using (∞)

open import Relation.Binary using (IsEquivalence; Symmetric; Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Definitions
open import Relations.Semantic using (_⊢_≣ᶜ_; ≣ᶜ-IsEquivalence; ≣ᶜ-congruent; _is-at-least-as-expressive-as_)

import Data.IndexedSet
private module ISet A = Data.IndexedSet (VariantSetoid ∞ A)
open import Util.Finity

open import Lang.Properties.Soundness
open import Lang.Properties.NonEmpty
```

## Conclusions

```agda
open import Data.Nat using (ℕ; suc)

soundness-by-finite-semantics : ∀ {L : VariabilityLanguage}
  → FiniteSemantics L
    -----------------------------
  → Sound L
soundness-by-finite-semantics {L} L-has-finite-semantics {A} e =
      size fin
    , ⟦ e ⟧ ∘ enumerate-configuration
    , re-index
        {_≈ᵃ_ = _≡_}
        enumerate-configuration
        ⟦ e ⟧
        (enumerate-is-surjective fin)
        (IsEquivalence.sym (≣ᶜ-IsEquivalence e))
        (≣ᶜ-congruent e)
      where open ISet A using (re-index)
            fin = L-has-finite-semantics e
            enumerate-configuration = enumerate fin

            ⟦_⟧ : Expression A L → configuration L → Variant ∞ A
            ⟦_⟧ = semantics L ∘ get

            -- ∃c : NonEmpty L
            -- edec : (∀ {A} (e : Expression A L) → Decidable (e ⊢_≣ᶜ_)) -- this assumption is ugly :(

            -- _≟ᶜ_ : Decidable (e ⊢_≣ᶜ_)
            -- _≟ᶜ_ = edec e

            -- re-indexation : Fin (suc (size fin)) → configuration L
            -- re-indexation zero = ∃c e
            -- re-indexation (suc n) = enumerate fin n

            -- sur : Surjective _≡_ (e ⊢_≣ᶜ_) re-indexation
            -- sur config with config ≟ᶜ ∃c e
            -- ...        | yes e⊢config≣ᶜ∃ce = zero , Eq.sym e⊢config≣ᶜ∃ce
            -- ...        | no _ with enumerate-is-surjective fin config
            -- ...               | fst , snd = suc fst , snd

soundness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage}
  → Sound L₁
  → L₁ is-at-least-as-expressive-as L₂
    ----------------------------------
  → Sound L₂
soundness-by-expressiveness {L₁} {L₂} L₁-sound L₂-to-L₁ {A} e₂ with L₂-to-L₁ e₂
... | e₁ , e₂≅e₁ with L₁-sound e₁
...   | n , vs , vs≅e₁ = n , vs , ≅-trans vs≅e₁ (≅-sym e₂≅e₁)
  where open ISet A using (_≅_; ≅-trans; ≅-sym)

-- re-export the theorem that we can conclude expressiveness for a complete and a sound language
open import Lang.Properties.Conclude.Completeness using (
  expressiveness-by-completeness-and-soundness
  ) public
```

