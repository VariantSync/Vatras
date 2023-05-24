# The set of variants described by a language can be enumerated

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.Properties.EnumerableSemantics where
```

## Imports

```agda
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)

open import Function using (_∘_; Surjective; Congruent)
open import Size using (∞)

open import Relation.Binary using (IsEquivalence; Symmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Definitions
open import Relations.Semantic using (_⊢_≣ᶜ_; ≣ᶜ-IsEquivalence; ≣ᶜ-congruent)

import Data.Multiset
private module Iso A = Data.Multiset (VariantSetoid ∞ A)
```

## Definitions

```agda
record EnumerableSemanticsIn (L : VariabilityLanguage) (A : Domain) : Set₁ where
  open Iso A using (_≅_; re-index)
  private ⟦_⟧ = semantics L

  field
    {-|
    Computes a lower bound of the number of variants described by a given expression.
    The expression should thus describe at least the returned amount of variants.
    -}
    variant-count-1 : Expression A L → ℕ
    pick            : (e : Expression A L) → Fin (suc (variant-count-1 e)) → configuration L
    pick-surjective : ∀ {e} → Surjective _≡_ (e ⊢_≣ᶜ_) (pick e)

  enumerate : (e : Expression A L) → ∃[ n ] (Σ[ vsetₑ ∈ VSet A n ] (vsetₑ ≅ ⟦ get e ⟧))
  enumerate e =
      variant-count-1 e
    , ⟦ get e ⟧ ∘ pick e
    , re-index
        {_≈ᵃ_ = _≡_}
        (pick e)
        ⟦ get e ⟧
        sur sym con
      where sur : Surjective _≡_ (e ⊢_≣ᶜ_) (pick e)
            sur = pick-surjective {e}

            sym : Symmetric (e ⊢_≣ᶜ_)
            sym = IsEquivalence.sym (≣ᶜ-IsEquivalence e)

            con : Congruent (e ⊢_≣ᶜ_) _≡_ (⟦ get e ⟧)
            con = ≣ᶜ-congruent e
open EnumerableSemanticsIn public

record EnumerableSemantics (L : VariabilityLanguage) : Set₁ where
  field
    within : ∀ {A} → EnumerableSemanticsIn L A
open EnumerableSemantics public
```



