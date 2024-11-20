```
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.FST.IncompleteOnRose {F : 𝔽} where

open import Size using (Size; ∞)
open import Data.Product using (∃-syntax; ∄-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Vatras.Framework.Variants using (Rose; rose-leaf)
open import Vatras.Lang.FST F
```

## Feature Structure Trees are Incomplete

We prove that FST SPLs are an incomplete variability language, when
assuming rose trees as variant type.
The proof works similarly as for option calculus.
The idea is that feature structure trees cannot encode variant generators
with exactly two disjunct variants.

```agda
open import Data.Fin using (zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Vatras.Framework.VariantGenerator using (VariantGenerator)
open import Vatras.Framework.Properties.Completeness using (Incomplete)

variant-0 = rose-leaf {A = (ℕ , ℕ._≟_)} 0
variant-1 = rose-leaf {A = (ℕ , ℕ._≟_)} 1

variants-0-and-1 : VariantGenerator (Rose ∞) (ℕ , ℕ._≟_) 1
variants-0-and-1 zero       = variant-0
variants-0-and-1 (suc zero) = variant-1

does-not-describe-variants-0-and-1 :
  ∀ {i : Size}
  → (e : Impose.SPL (ℕ , ℕ._≟_))
  → ∃[ c ] (variant-0 ≡ ⟦ e ⟧ c)
  → ∄[ c ] (variant-1 ≡ ⟦ e ⟧ c)
does-not-describe-variants-0-and-1 (zero Impose.◀ features) _ ()
does-not-describe-variants-0-and-1 (suc root Impose.◀ features) ()

FST-is-incomplete : Incomplete (Rose ∞) FSTL
FST-is-incomplete complete with complete variants-0-and-1
FST-is-incomplete complete | e , e⊆vs , vs⊆e = does-not-describe-variants-0-and-1 e (e⊆vs zero) (e⊆vs (suc zero))
```
