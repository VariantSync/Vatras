```agda
module Framework.VariabilityLanguage where

open import Data.List using (List)

open import Framework.Definitions
```

## Core definitions

The semantics of variability languages is a set of variants.
We model this set in terms of a function (see IndexedSet).
Hence, the semantics is a function that configures an expression
`e : E A` to a variant `v : V A` for any domain `A : 𝔸`.
```agda
data Variant : 𝕍 where
  artifact : ∀ {A : 𝔸} → atoms A → List (Variant A) → Variant A

𝔼-Semantics : 𝕂 → 𝔼 → Set₁
𝔼-Semantics K E = ∀ {A : 𝔸} → E A → K → Variant A

record VariabilityLanguage : Set₁ where
  constructor ⟪_,_,_⟫
  field
    Expression : 𝔼
    Config     : 𝕂
    Semantics  : 𝔼-Semantics Config Expression
open VariabilityLanguage public
```
