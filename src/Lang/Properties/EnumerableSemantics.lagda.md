# The set of variants described by a language can be enumerated

## Options

```agda
{-# OPTIONS --sized-types #-}
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

open import Function using (_∘_)
open import Size using (∞)

open import Definitions

import Data.Multiset
private module Iso A = Data.Multiset (VariantSetoid ∞ A)
```

## Definitions

```agda
record EnumerableSemanticsIn (L : VariabilityLanguage) (A : Domain) : Set₁ where
  open Iso A using (_≅_)
  private ⟦_⟧ = semantics L

  field
    variant-count-1 : Expression A L → ℕ
    pick            : (e : Expression A L) → Fin (suc (variant-count-1 e)) → configuration L
    pick-preserves  : ∀ {e} → (⟦ get e ⟧ ∘ pick e) ≅ ⟦ get e ⟧

  enumerate : (e : Expression A L) → ∃[ n ] (Σ[ vsetₑ ∈ VSet A n ] (vsetₑ ≅ ⟦ get e ⟧))
  enumerate e = variant-count-1 e , ⟦ get e ⟧ ∘ pick e , pick-preserves
open EnumerableSemanticsIn public

record EnumerableSemantics (L : VariabilityLanguage) : Set₁ where
  field
    within : ∀ {A} → EnumerableSemanticsIn L A
open EnumerableSemantics public
```



