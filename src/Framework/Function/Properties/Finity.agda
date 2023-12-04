open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
module Framework.Function.Properties.Finity
  (O : Setoid 0ℓ 0ℓ)
  where

open Setoid O

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; proj₁; _,_; ∃-syntax; Σ-syntax)
open import Function using (_∘_; Surjective; Congruent)

open import Relation.Binary using (IsEquivalence; Symmetric; Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.FunctionLanguage as FL
open FL.FunctionLanguage
open FL.Comp O
open import Framework.Function.Relation.Index O using (_∋_⊢_≣ⁱ_; ≣ⁱ-IsEquivalence; ≣ⁱ-congruent; ≣ⁱ-setoid)
open import Framework.Function.Properties.Soundness O
open import Data.IndexedSet O using (IndexedSet; _≅_; ≅-trans; ≅-sym; re-index)
open import Util.Enumerable

HasEnumerableNonEmptySemantics : FunctionLanguage Carrier → Set
HasEnumerableNonEmptySemantics L = ∀ e → EnumerableAndNonEmpty (≣ⁱ-setoid L e)

-- TODO: Move the following to the variability package?
soundness-from-enumerability : ∀ {L : FunctionLanguage Carrier}
  → HasEnumerableNonEmptySemantics L
    --------------------------------
  → Sound ℕ (Fin ∘ suc) L
soundness-from-enumerability {L} L-has-finite-semantics e =
      size fin
    , ⟦ e ⟧ ∘ enumerate-configuration
    , re-index
        {_≈ᵃ_ = _≡_}
        enumerate-configuration
        ⟦ e ⟧
        (enumerate-is-surjective fin)
        (IsEquivalence.sym (≣ⁱ-IsEquivalence L e))
        (≣ⁱ-congruent L e)
      where ⟦_⟧ = Semantics L
            fin = L-has-finite-semantics e
            enumerate-configuration = enumerate fin
