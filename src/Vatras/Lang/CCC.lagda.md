# Core Choice Calculus

```agda
open import Vatras.Framework.Definitions
module Vatras.Lang.CCC (Dimension : 𝔽) where
```

## Imports
```agda
open import Data.List as List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ)

open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage using (𝔼-Semantics; VariabilityLanguage; ⟪_,_,_⟫)
open import Vatras.Util.List using (find-or-last)
```

## Syntax

A core choice calculus expression is either an artifact `a -< es >-` (just as in [rose trees](../Framework/Variants.agda))
or a choice `D ⟨ as ⟩` with an arbitrarily many but at least one alternative `as`.
```agda
data CCC : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (CCC i A) → CCC (↑ i) A
   _⟨_⟩ : ∀ {i A} → Dimension → List⁺ (CCC i A) → CCC (↑ i) A
```

## Semantics

The core choice calculus has denotational semantics.
Semantics for choice calculus have been defined in different ways.
- As a set of pairs `Configuration × Variant`
- As a configuration function `Configuration → Variant` that generates variants from configurations.

The second definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by choosing an alternative.
While choices have a fixed and finite amount of alternatives, we allow the configuration to produce
any natural number for simplicity here (in case of an overlow, we will just pick the last alternative).
This formulation is a simplification of the original choice calculus in which alternatives are identified by _tags_
and then configurations choose tags.
The simplification here is analogous to how de Bruijn indices simplify lambda calculus.
```agda
Configuration : ℂ
Configuration = Dimension → ℕ
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., a number larger than the amount of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to avoid complex error handling or typing rules to ensure that a  configuration only produces valid tags.
```agda
⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics (Rose ∞) Configuration (CCC i)
⟦ a -< cs >- ⟧ c = a V.-< List.map (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ cs ⟩   ⟧ c = ⟦ find-or-last (c D) cs ⟧ c

CCCL : ∀ {i : Size} → VariabilityLanguage (Rose ∞)
CCCL {i} = ⟪ CCC i , Configuration , ⟦_⟧ ⟫
```
