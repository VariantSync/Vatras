```agda
module Framework.VariabilityLanguage where

open import Framework.Definitions
```

## Core definitions

The semantics of variability languages is a set of variants.
We model this set in terms of a function (see IndexedSet).
Hence, the semantics is a function that configures an expression
`e : E A` to a variant `v : V A` for any domain `A : 𝔸`.
```agda
𝔼-Semantics : 𝕍 → ℂ → 𝔼 → Set₁
𝔼-Semantics V K E = ∀ {A : 𝔸} → E A → K → V A

record VariabilityLanguage (V : 𝕍) : Set₂ where
  constructor ⟪_,_,_⟫
  field
    Expression : 𝔼
    Config     : ℂ
    Semantics  : 𝔼-Semantics V Config Expression
open VariabilityLanguage public
```
