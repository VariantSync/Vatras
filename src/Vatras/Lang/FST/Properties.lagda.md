```
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.FST.Properties {F : 𝔽} where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (∃-syntax; ∄-syntax; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Vatras.Framework.Variants using (Rose; _-<_>-; rose-leaf; children-equality)
open import Vatras.Lang.FST F
```

## Neighbor Problem

We formalize the neighbor problem.
This theorem states that FST SPLs can never
describe a variant in which two neighboring nodes have the same atom.
This theorem is a specialized form in which this variant is fixed to
  a -< b, b >-
for two any two atoms a, b.

```agda
cannotEncodeNeighbors : ∀ {A : 𝔸} (a b : atoms A) → ∄[ e ] (∃[ c ] ⟦ e ⟧ c ≡ a -< rose-leaf b ∷ rose-leaf b ∷ [] >-)
cannotEncodeNeighbors {A} a b (e , conf , ⟦e⟧c≡neighbors) =
  ¬Unique b (Eq.subst (λ l → Unique l) (children-equality ⟦e⟧c≡neighbors) (lemma (⊛-all (select conf (features e)))))
  where
  open Impose A

  lemma : ∀ (e : FSF) → Unique (forget-uniqueness e)
  lemma (_ Impose.⊚ (unique , _)) = unique

  ¬Unique : ∀ (a : atoms A) → ¬ Unique (a -< [] >- ∷ a -< [] >- ∷ [])
  ¬Unique a ((a≢a ∷ []) ∷ [] ∷ []) = a≢a refl
```
