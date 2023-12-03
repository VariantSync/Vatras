# Theorems to Prove Soundness

```agda
open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
module Framework.Function.Proof.Soundness
  (O : Setoid 0ℓ 0ℓ)
  (I : Set)
  where

open Setoid O

open import Data.Product using (_,_)
open import Framework.FunctionLanguage as FL
open FL.FunctionLanguage
open FL.Comp {0ℓ} {O}
open import Data.IndexedSet O using (≅-trans; ≅-sym)
open import Framework.Function.Properties.Soundness O I
```

## Conclusions

```agda
soundness-by-expressiveness : ∀ {L₁ L₂ : FunctionLanguage Carrier}
  → Sound L₁
  → L₁ ≽ L₂
    --------
  → Sound L₂
soundness-by-expressiveness L₁-sound L₂-to-L₁ e₂ with L₂-to-L₁ e₂
... | e₁ , e₂≅e₁ with L₁-sound e₁
...   | m , m≅e₁ = m , ≅-trans m≅e₁ (≅-sym e₂≅e₁)

-- re-export the theorem that we can conclude expressiveness for a complete and a sound language
open import Framework.Function.Proof.Completeness O I using (
  expressiveness-by-completeness-and-soundness
  ) public
```

