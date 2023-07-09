# The set of variants described by a language can be enumerated

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Framework.Properties.Soundness where
```

## Imports

```agda
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; Σ-syntax)

open import Function using (_∘_; Surjective)
open import Size using (∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Definitions
open import Relations.Semantic using (≣ᶜ-setoid)

import Data.IndexedSet
private module ISet A = Data.IndexedSet (VariantSetoid ∞ A)
open import Util.Finity using (FiniteAndNonEmpty)
```

## Definitions

```agda
Sound : VariabilityLanguage → Set₁
Sound L = ∀ {A}
  → (e : Expression A L)
    ------------------------------
  → ∃[ n ] (Σ[ vs ∈ VMap A n ]
      (let open ISet A using (_≅_)
           ⟦_⟧ = semantics L ∘ get
        in vs ≅ ⟦ e ⟧))

Unsound : VariabilityLanguage → Set₁
Unsound L = ¬ (Sound L)

FiniteSemantics : (L : VariabilityLanguage) → Set₁
FiniteSemantics L = ∀ {A} (e : Expression A L) → FiniteAndNonEmpty (≣ᶜ-setoid e)

-- record FiniteSemantics (A : 𝔸) (L : VariabilityLanguage) : Set₁ where
--   field
--     {-|
--     Computes a lower bound of the number of variants described by a given expression.
--     The expression should thus describe at least the returned amount of variants - 1.
--     -}
--     # : Expression A L → ℕ

--     {-|
--     Identifies each configuration of a given expression by a natural number.
--     This is the first step of proving that there exist only a finite amount of
--     configurations, and thus variants described by the expression.
--     -}
--     pick : (e : Expression A L) → Fin (suc (# e)) → configuration L

--     {-|
--     Identification of configurations has to be surjective:
--     Every configuration is indexed.
--     While there might be infinitely many configurations, there must be a finite subset
--     of configurations that describes all variants.
--     This means that surjectivity actually means:
--     For every configuration, there exists a configuration that is picked by pick and
--     is semantically equivalent (w.r.t., e ⊢_≣ᶜ_).
--     Thus, pick must be be surjective on the subset of unique configurations within a
--     given expression e.
--     -}
--     pick-surjective : ∀ {e} → Surjective _≡_ (_⊢_≣ᶜ_ e) (pick e)
-- open FiniteSemantics public_≈
```

