```agda
open import Vatras.Framework.Definitions using (𝔽)
module Vatras.Lang.OC.IncompleteOnRose {Option : 𝔽} where

open import Size using (Size; ∞)
open import Data.Fin using (zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax; ∄-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Vatras.Framework.Variants using (Rose; rose-leaf)
open import Vatras.Framework.VariantGenerator (Rose ∞) (ℕ , ℕ._≟_) using (VariantGenerator)
open import Vatras.Framework.Properties.Completeness (Rose ∞) using (Incomplete)
open import Vatras.Lang.OC Option using (WFOC; Root; ⟦_⟧; WFOCL)
```

We prove incompleteness by showing that there exists at least one set of variants that cannot be described by option calculus.
In particular, any set of variants that includes two entirely distinct variants cannot be expressed because options cannot encode constraints such as alternatives in choice calculus.
As our counter example, we use the set `{0, 1}` as our variants:
```agda
variant-0 = rose-leaf {A = (ℕ , ℕ._≟_)} 0
variant-1 = rose-leaf {A = (ℕ , ℕ._≟_)} 1

variants-0-and-1 : VariantGenerator 1
variants-0-and-1 zero = variant-0
variants-0-and-1 (suc zero) = variant-1
```

We stick to this concrete counter example instead of formulating the set of unrepresentable variants here to make the proof not more complicated than necessary.

We now prove that any well-formed option calculus expression `e` cannot be configured to `0` and `1` at the same time. The reason is that the expression `e` always has a domain element at the top. This element is always included in the variant and cannot simultaneously be `0` and `1`.
So we show that given an expression `e`, a proof that `e` can be configured to `0`, and a proof that `e` can be configured to `1`, we eventually conclude falsehood.

```agda
does-not-describe-variants-0-and-1 :
  ∀ {i : Size}
  → (e : WFOC i (ℕ , ℕ._≟_))
  → ∃[ c ] (variant-0 ≡ ⟦ e ⟧ c)
  → ∄[ c ] (variant-1 ≡ ⟦ e ⟧ c)
-- If e has 0 as root, it may be configured to 0 but never to 1.
does-not-describe-variants-0-and-1 (Root 0 es) ∃c→v0≡⟦e⟧c ()
-- if e has a number larger than 1 at the top, it cannot be configured to yield 0.
does-not-describe-variants-0-and-1 (Root (suc n) es) ()
```

Finally, we can conclude incompleteness by showing that assuming completeness yields a contradiction using our definition above.
We pattern match on the assumed completeness evidence to unveil the expression `e` and the proofs that it can be configured to `0` and `1`.

```agda
OC-is-incomplete : Incomplete WFOCL
OC-is-incomplete assumed-completeness with assumed-completeness variants-0-and-1
... | e , ∀n→∃c→vn≡⟦e⟧ , _ = does-not-describe-variants-0-and-1 e (∀n→∃c→vn≡⟦e⟧ zero) (∀n→∃c→vn≡⟦e⟧ (suc zero))
```

**This is an important result!**
It shows that we need at least some constraints to be complete.
This is a justification for choice calculus defining variability annotations with constraints (being alternative) instead of being pure annotations.
Another way is to enrich the annotation language, for example using propositional logic.
