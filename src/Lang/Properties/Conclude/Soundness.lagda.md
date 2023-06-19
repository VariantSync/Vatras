# Theorems to Prove Soundness


```agda
{-# OPTIONS --sized-types #-}

module Lang.Properties.Conclude.Soundness where

open import Data.Product using (_,_)

open import Function using (_∘_; Surjective; Congruent)
open import Size using (∞)

open import Relation.Binary using (IsEquivalence; Symmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Definitions
open import Relations.Semantic using (_⊢_≣ᶜ_; ≣ᶜ-IsEquivalence; ≣ᶜ-congruent; _is-at-least-as-expressive-as_)

import Data.Multiset
private module MSet A = Data.Multiset (VariantSetoid ∞ A)

open import Lang.Properties.Soundness
```

## Conclusions

```agda
soundness-by-finite-semantics : ∀ {L : VariabilityLanguage}
  → (∀ {A} → FiniteSemantics A L)
    -----------------------------
  → Sound L
soundness-by-finite-semantics {L} fin {A} e =
    let open MSet A using (re-index)
     in
      # fin e
    , ⟦ e ⟧ ∘ re-indexation
    , re-index
        {_≈ᵃ_ = _≡_}
        re-indexation
        ⟦ e ⟧
        sur sym con
      where ⟦_⟧ = semantics L ∘ get
            re-indexation = pick fin e

            sur : Surjective _≡_ (e ⊢_≣ᶜ_) re-indexation
            sur = pick-surjective fin

            sym : Symmetric (e ⊢_≣ᶜ_)
            sym = IsEquivalence.sym (≣ᶜ-IsEquivalence e)

            con : Congruent (e ⊢_≣ᶜ_) _≡_ ⟦ e ⟧
            con = ≣ᶜ-congruent e

soundness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage}
  → Sound L₁
  → L₁ is-at-least-as-expressive-as L₂
    ----------------------------------
  → Sound L₂
soundness-by-expressiveness {L₁} {L₂} L₁-sound L₂-to-L₁ {A} e₂ with L₂-to-L₁ e₂
... | e₁ , e₂≅e₁ with L₁-sound e₁
...   | n , vs , vs≅e₁ = n , vs , ≅-trans vs≅e₁ (≅-sym e₂≅e₁)
  where open MSet A using (_≅_; ≅-trans; ≅-sym)

-- re-export the theorem that we can conclude expressiveness for a complete and a sound language
open import Lang.Properties.Conclude.Completeness using (
  expressiveness-by-completeness-and-soundness
  ) public
```

