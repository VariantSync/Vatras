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
open FL.Comp {0ℓ} {O}
open import Framework.Function.Relation.Index O using (_∋_⊢_≣ⁱ_; ≣ⁱ-IsEquivalence; ≣ⁱ-congruent; ≣ⁱ-setoid)
open import Framework.Function.Properties.Soundness O
open import Data.IndexedSet O using (IndexedSet; _≅_; ≅-trans; ≅-sym; re-index)
open import Util.Enumerable

IsFiniteAndNotEmpty : FunctionLanguage Carrier → Set
IsFiniteAndNotEmpty ⟪ Expr , _ , ⟦_⟧ ⟫ =
  ∀ (e : Expr)
    --------------------------------
  → ∃[ n ] (Σ[ m ∈ IndexedSet (Fin (suc n)) ] (m ≅ ⟦ e ⟧))

HasEnumerableNonEmptySemantics : FunctionLanguage Carrier → Set
HasEnumerableNonEmptySemantics L = ∀ e → EnumerableAndNonEmpty (≣ⁱ-setoid L e)

finity-from-enumerability : ∀ {L : FunctionLanguage Carrier}
  → HasEnumerableNonEmptySemantics L
    --------------------------------
  → IsFiniteAndNotEmpty L
finity-from-enumerability {L} L-has-finite-semantics e =
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

soundness-from-finity : ∀ {L : FunctionLanguage Carrier}
  → (fin : IsFiniteAndNotEmpty L)
  → Sound ℕ (Fin ∘ suc) L
soundness-from-finity fin e with fin e
... | n , m , m≅⟦e⟧ = n , m , m≅⟦e⟧
