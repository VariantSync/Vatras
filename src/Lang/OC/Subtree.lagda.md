```agda
module Lang.OC.Subtree where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (Sublist; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (∞)

open import Framework.Definitions using (𝔽; 𝔸; atoms)
open import Framework.Variants as V hiding (_-<_>-)
open import Lang.OC
open Sem (Rose ∞) Artifact∈ₛRose
open import Util.AuxProofs using (true≢false)
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

Implies : {F : 𝔽} → Configuration F → Configuration F → Set
Implies {F} c₁ c₂ = (f : F) → c₁ f ≡ true → c₂ f ≡ true

mutual
  subtreeₒ : ∀ {F : 𝔽} {A : 𝔸} → (e : OC F ∞ A) → (c₁ c₂ : Configuration F) → Implies c₁ c₂ → MaybeSubtree (⟦ e ⟧ₒ c₁) (⟦ e ⟧ₒ c₂)
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

  subtreeₒ-recurse : ∀ {F : 𝔽} {A : 𝔸} → (cs : List (OC F ∞ A)) → (c₁ c₂ : Configuration F) → Implies c₁ c₂ → Sublist Subtree (⟦ cs ⟧ₒ-recurse c₁) (⟦ cs ⟧ₒ-recurse c₂)
  subtreeₒ-recurse [] c₁ c₂ c₁-implies-c₂ = []
  subtreeₒ-recurse (c ∷ cs) c₁ c₂ c₁-implies-c₂ with ⟦ c ⟧ₒ c₁ | ⟦ c ⟧ₒ c₂ | subtreeₒ c c₁ c₂ c₁-implies-c₂
  ... | .nothing | .nothing | neither = subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
  ... | .nothing | just c' | one = c' ∷ʳ subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
  ... | .(just _) | .(just _) | both p = p ∷ subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂
```

If two configurations are related, their variants are also related.  This result
is enabled by the fact that OC cannot encode alternatives but only include or
exclude subtrees. Hence, a subtree present in `c₂` can be removed, without any
accidental additions anywhere in the variant, by configuring an option above it
to `false` in `c₁`. However, the reverse is ruled out by the `Implies`
assumption.
```agda
subtree : ∀ {F : 𝔽} {A : 𝔸} → (e : WFOC F ∞ A) → (c₁ c₂ : Configuration F) → Implies c₁ c₂ → Subtree (⟦ e ⟧ c₁) (⟦ e ⟧ c₂)
subtree {F} {A} (Root a cs) c₁ c₂ c₁-implies-c₂ = subtrees (subtreeₒ-recurse cs c₁ c₂ c₁-implies-c₂)
```
