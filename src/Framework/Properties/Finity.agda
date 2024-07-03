open import Framework.Definitions using (𝕍)

{-|
This module contains definition to say that
a variability language denotes a finite set of variants.
-}
module Framework.Properties.Finity (V : 𝕍) where

open import Data.Product using (_,_)
open import Function using (_∘_; Surjective; Congruent)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Framework.VariabilityLanguage
open import Framework.Relation.Index V using (_∋_⊢_≣ⁱ_; ≣ⁱ-IsEquivalence; ≣ⁱ-congruent; ≣ⁱ-setoid)
open import Framework.Properties.Soundness V
open import Framework.Relation.Expression V
open import Data.EqIndexedSet
open import Util.Enumerable

{-|
A variability language satisfies this predicate
if its variants can be enumerated and if it denotes at least
one variant.
-}
HasEnumerableNonEmptySemantics : VariabilityLanguage V → Set₁
HasEnumerableNonEmptySemantics L = ∀ {A} e → EnumerableAndNonEmpty (≣ⁱ-setoid {A} L e)

{-|
If we know that the semantic domain of a variability language can
be enumerated (i.e., is finite) and is not empty,
we can prove that the language is sound.
-}
soundness-from-enumerability : ∀ {L : VariabilityLanguage V}
  → HasEnumerableNonEmptySemantics L
    --------------------------------
  → Sound L
soundness-from-enumerability {L} L-has-finite-semantics {A} e =
      size fin
    , ⟦ e ⟧ ∘ enumerate-configuration
    , re-index
        {_≈ᵃ_ = _≡_}
        enumerate-configuration
        ⟦ e ⟧
        (enumerate-is-surjective fin)
        (Eq._≡_.refl)
        (IsEquivalence.sym (≣ⁱ-IsEquivalence L e))
        (≣ⁱ-congruent L e)
      where ⟦_⟧ = Semantics L
            fin = L-has-finite-semantics e
            enumerate-configuration = enumerate fin
