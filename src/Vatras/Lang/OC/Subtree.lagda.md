# Subtrees in Variants and Option Calculus

This module introduces reasoning on subtrees of variants and in option calculus.

```agda
module Vatras.Lang.OC.Subtree where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (Sublist; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (∞)

open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
open import Vatras.Framework.Variants as V hiding (_-<_>-)
open import Vatras.Util.AuxProofs using (true≢false)
```

Relates two variants iff the first argument is a subtree of the second argument.
In other words: if some artifacts (including all their children) can be removed
from the second variant to obtain the first variant exactly.
```agda
data Subtree {A : 𝔸} : Rose ∞ A → Rose ∞ A → Set₁ where
  subtrees : {a : atoms A} → {cs₁ cs₂ : List (Rose ∞ A)} → Sublist Subtree cs₁ cs₂ → Subtree (a V.-< cs₁ >-) (a V.-< cs₂ >-)
```

Relates two optional variants using `Subtree`. This is mostly useful for
relating `⟦_⟧ₒ` whereas `Subtree` is mostly used to relate `⟦_⟧`. It has the
same semantics as `Subtree` but allows for the removal of the root artifact,
which is fixed in `Subtree`.
```agda
data MaybeSubtree {A : 𝔸} : Maybe (Rose ∞ A) → Maybe (Rose ∞ A) → Set₁ where
  neither : MaybeSubtree nothing nothing
  one : {c : Rose ∞ A} → MaybeSubtree nothing (just c)
  both : {c₁ c₂ : Rose ∞ A} → Subtree c₁ c₂ → MaybeSubtree (just c₁) (just c₂)
```

```agda
module _ {F : 𝔽} where
  open import Vatras.Lang.OC F using (OC; _❲_❳; _-<_>-; WFOC; Root; Configuration; ⟦_⟧; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse)

  Implies : Configuration → Configuration → Set
  Implies c₁ c₂ = (f : F) → c₁ f ≡ true → c₂ f ≡ true
```

If two configurations are related, their variants are also related. This result
is enabled by the fact that OC cannot encode alternatives but only include or
exclude subtrees. Hence, a subtree present in `c₂` can be removed, without any
accidental additions anywhere in the variant, by configuring an option above it
to `false` in `c₁`. However, the reverse is ruled out by the `Implies`
assumption.

The following lemmas require mutual recursion because they are properties about
functions (`⟦_⟧ₒ` and `⟦_⟧ₒ-recurse`) which are also defined mutually recursive.
```agda
  mutual
    subtreeₒ : ∀ {A : 𝔸} → (e : OC ∞ A) → (c₁ c₂ : Configuration) → Implies c₁ c₂ → MaybeSubtree (⟦ e ⟧ₒ c₁) (⟦ e ⟧ₒ c₂)
    subtreeₒ (a -< cs >-) c₁ c₂ c₁-implies-c₂ = both (subtrees (subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂))
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ with c₁ f in c₁-f | c₂ f in c₂-f
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | false | false = neither
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | false | true with ⟦ c ⟧ₒ c₂
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | false | true | just _ = one
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | false | true | nothing = neither
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | true | false = ⊥-elim (true≢false refl (Eq.trans (Eq.sym (c₁-implies-c₂ f c₁-f)) c₂-f))
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | true | true with ⟦ c ⟧ₒ c₁ | ⟦ c ⟧ₒ c₂ | subtreeₒ c c₁ c₂ c₁-implies-c₂
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | true | true | .nothing | .nothing | neither = neither
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | true | true | .nothing | .(just _) | one = one
    subtreeₒ (f ❲ c ❳) c₁ c₂ c₁-implies-c₂ | true | true | .(just _) | .(just _) | both p = both p
```

From `subtreeₒ`, we know that `map (λ c → ⟦ c ⟧ₒ c₁)` can produce `nothing`s
instead of `just`s at some outputs of `map (λ c → ⟦ c ⟧ₒ c₂)`. All other
elements must be the same. Hence, `catMaybes` results in a sublist.
```agda
    subtreeₒ-recurse : ∀ {A : 𝔸} → (cs : List (OC ∞ A)) → (c₁ c₂ : Configuration) → Implies c₁ c₂ → Sublist Subtree (⟦ cs ⟧ₒ-recurse c₁) (⟦ cs ⟧ₒ-recurse c₂)
    subtreeₒ-recurse [] c₁ c₂ c₁-implies-c₂ = []
    subtreeₒ-recurse (c ∷ cs) c₁ c₂ c₁-implies-c₂ with ⟦ c ⟧ₒ c₁ | ⟦ c ⟧ₒ c₂ | subtreeₒ c c₁ c₂ c₁-implies-c₂
    ... | .nothing | .nothing | neither = subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
    ... | .nothing | just c' | one = c' ∷ʳ subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
    ... | .(just _) | .(just _) | both p = p ∷ subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
```

This theorem still holds if we guarantee that there is an artifact at the root.
```agda
  subtree : ∀ {A : 𝔸} → (e : WFOC ∞ A) → (c₁ c₂ : Configuration) → Implies c₁ c₂ → Subtree (⟦ e ⟧ c₁) (⟦ e ⟧ c₂)
  subtree (Root a cs) c₁ c₂ c₁-implies-c₂ = subtrees (subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂)
```
