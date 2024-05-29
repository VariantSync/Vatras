open import Framework.Definitions using (𝔽; 𝔸; atoms)
open import Relation.Binary using (DecidableEquality)

module Translation.Lang.FST-to-VariantList (F : 𝔽) (_==ꟳ_ : DecidableEquality F) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _⁺++⁺_)
import Data.List.NonEmpty.Properties as List⁺
import Data.List.Properties as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _<_; s≤s; z≤n; _+_)
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (∞)

import Data.EqIndexedSet as IndexedSet
open import Framework.Compiler using (LanguageCompiler)
import Framework.Relation.Expressiveness
open import Framework.Relation.Function using (from; to)
open import Framework.Variants using (Rose; _-<_>-)
open import Util.List using (find-or-last; map-find-or-last; find-or-last-prepend-+; find-or-last-append)

open Framework.Relation.Expressiveness (Rose ∞) using (_≽_; expressiveness-from-compiler)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All
open FST using (FSTL)
open FST.Impose using (SPL; Feature)
module Impose {F} {A} = FST.Impose F A
open Impose using (_◀_; _::_; name; select; forget-uniqueness; ⊛-all)
open VariantList using (VariantList; VariantListL)

config-with : Bool → F → FST.Configuration F → FST.Configuration F
config-with value f c f' with f ==ꟳ f'
config-with value f c f' | yes _ = value
config-with value f c f' | no  _ = c f'

{-|
Given a list of feature names,
generates all possible configurations.
If there are no features, a single configuration deselecting all features
will be returned as a base case.
Beware that the size of the returned list is 2^(length l) where
l is the input list of features.
-}
configs : List F → List⁺ (FST.Configuration F)
configs [] = (λ _ → false) ∷ []
configs (f ∷ fs) = List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)

{-|
Translates a feature-based product line into a variant list
by enumerating all possible configurations and then deriving
all possible variants.
A crucial observation is that each index in the list is associated to
exactly one unique configuration _and_ its respective, not neccessarily unique, variant.
(conf and fnoc below rely on exactly this correspondence.)
-}
translate : ∀ {A : 𝔸} → SPL F A → VariantList A
translate {A} (a ◀ fs) = List⁺.map (λ c → FST.⟦ a ◀ fs ⟧ c) (configs (map name fs))

conf' : FST.Configuration F → List F → ℕ
conf' c [] = 0
conf' c (f ∷ fs) with c f
conf' c (f ∷ fs) | true = List⁺.length (configs fs) + conf' c fs
conf' c (f ∷ fs) | false = conf' c fs

{-|
Translates an FST configuration to a VariantList configuration
matching a feature-based SPL that was translated via the 'translate' function above.
The translation works by computing the index of the respective variant in the
resulting list, which is possible because the order of variants in the list solely
depends on the order in which configurations were generated by 'translate'.
-}
conf : ∀ {A : 𝔸} → (e : SPL F A) → FST.Configuration F → VariantList.Configuration
conf {A} (_ ◀ fs) c = conf' c (map name fs)

{-|
Translates a VariantList configuration back to a FST configuration
matching a feature-based SPL that was translated via the 'translate' function above.
The translation works by a lookup:
An index pointing to an FST variant in the list corresponds to exactly one unique
configuration which was enumerated by the 'configs' function.
So we can just enumerate all configurations again, and then pick the configuration at
the respective index.
-}
fnoc : ∀ {A : 𝔸} → (e : SPL F A) → VariantList.Configuration → FST.Configuration F
fnoc {A} (_ ◀ fs) n = find-or-last n (configs (map name fs))

{-|
An index computed by conf' is always in bounds
-}
conf'<configs : ∀ (c : FST.Configuration F) (fs : List F)
  → conf' c fs < List⁺.length (configs fs)
conf'<configs c [] = s≤s z≤n
conf'<configs c (f ∷ fs) with c f
conf'<configs c (f ∷ fs) | true =
  begin-strict
    List⁺.length (configs fs) + conf' c fs
  <⟨ ℕ.+-monoʳ-< (List⁺.length (configs fs)) (conf'<configs c fs) ⟩
    List⁺.length (configs fs) + List⁺.length (configs fs)
  ≡⟨ Eq.cong₂ _+_ (List⁺.length-map (config-with false f) (configs fs)) (List⁺.length-map (config-with true f) (configs fs)) ⟨
    List⁺.length (List⁺.map (config-with false f) (configs fs)) + List⁺.length (List⁺.map (config-with true f) (configs fs))
  ≡⟨ List.length-++ (List⁺.toList (List⁺.map (config-with false f) (configs fs))) ⟨
    List⁺.length (List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs))
  ≡⟨⟩
    List⁺.length (configs (f ∷ fs))
  ∎
  where
  open ℕ.≤-Reasoning
conf'<configs c (f ∷ fs) | false =
  begin-strict
    conf' c fs
  <⟨ conf'<configs c fs ⟩
    List⁺.length (configs fs)
  ≡⟨ List⁺.length-map (config-with false f) (configs fs) ⟨
    List⁺.length (List⁺.map (config-with false f) (configs fs))
  ≤⟨ ℕ.m≤m+n (List⁺.length (List⁺.map (config-with false f) (configs fs))) (List⁺.length (List⁺.map (config-with true f) (configs fs))) ⟩
    List⁺.length (List⁺.map (config-with false f) (configs fs)) + List⁺.length (List⁺.map (config-with true f) (configs fs))
  ≡⟨ List.length-++ (List⁺.toList (List⁺.map (config-with false f) (configs fs))) ⟨
    List⁺.length (List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs))
  ≡⟨⟩
    List⁺.length (configs (f ∷ fs))
  ∎
  where
  open ℕ.≤-Reasoning

{-|
Proof of correctness of the 'config-with' function.
When mutating a configuration c to set the value of a specific feature f to
a fixed value b, the mutated configuration will return exactly this value b for f.
-}
config-with-≡ : (b : Bool) → (f : F) → (c : FST.Configuration F) → config-with b f c f ≡ b
config-with-≡ b f c with f ==ꟳ f
config-with-≡ b f c | no f≢f = ⊥-elim (f≢f refl)
config-with-≡ b f c | yes _ = refl

{-|
Proof that the 'config-with' function does nothing else than intended:
It does not mutate the selection of any feature f' different from the feature f
whose value is fixed to a value b.
So for any such different feature, config-with returns the same value as the input
configuration.
-}
config-with-≢ : (b : Bool) → (f f' : F) → f ≢ f' → (c : FST.Configuration F) → config-with b f' c f ≡ c f
config-with-≢ b f f' f≢f' c with f' ==ꟳ f
config-with-≢ b f f' f≢f' c | no _ = refl
config-with-≢ b f f' f≢f' c | yes f'≡f = ⊥-elim (f≢f' (Eq.sym f'≡f))

{-|
Proof that a `config-with b f'` term can be eliminated
from a selection of configurations which all have this term in common.
This is not really a deep theorem.
This lemma is just factored out of `conf'-lemma` because it appears four times in there.

The idea is to evalute the selection on a specific feature `f`,
then the `config-with b f' c f` term can be evaluated.
-}
find-or-last-config-with : ∀ (c : FST.Configuration F) (b : Bool) (f f' : F) (fs : List F) (v : FST.Configuration F → Bool)
  → ((c : FST.Configuration F) → config-with b f' c f ≡ v c)
  → find-or-last (conf' c fs) (List⁺.map (config-with b f') (configs fs)) f ≡ v (find-or-last (conf' c fs) (configs fs))
find-or-last-config-with c b f f' fs v p =
    find-or-last (conf' c fs) (List⁺.map (config-with b f') (configs fs)) f
  ≡⟨ map-find-or-last (λ c → c f) (conf' c fs) (List⁺.map (config-with b f') (configs fs)) ⟩
    find-or-last (conf' c fs) (List⁺.map (λ c → c f) (List⁺.map (config-with b f') (configs fs)))
  ≡⟨ Eq.cong₂ find-or-last refl (List⁺.map-∘ (configs fs)) ⟨
    find-or-last (conf' c fs) (List⁺.map (λ c → config-with b f' c f) (configs fs))
  ≡⟨ Eq.cong₂ find-or-last refl (List⁺.map-cong p (configs fs)) ⟩
    find-or-last (conf' c fs) (List⁺.map v (configs fs))
  ≡⟨ map-find-or-last v (conf' c fs) (configs fs) ⟨
    v (find-or-last (conf' c fs) (configs fs))
  ∎
  where
  open Eq.≡-Reasoning

{-|
Proof that `fnoc` is the inverse of `conf`:
Given a particular configuration `c`,
enumerating all possible configurations,
and then evaluating the configuration at the index of `c` (which must be `c`),
is the same as evaluating `c` directly.

The lemma talks about `conf'` instead of `conf` and inlines `fnoc` to avoid extracting the `name` all the time.
Note that `f ∈ fs` is a necessary requirement
because configurations generated by `configs` are always set to `false` if `f ∉ fs`
whereas the given configuration `c` can have arbitrary values for any input.

The proof does an induction on the list of features
and makes a case analysis,
on wether we have found the feature in question (`f ==ꟳ f'`) and
on to what the original configuration evaluates to (`c f'`).

All cases start by selecting the correct sublist of `configs`.
Either the right half, if `c f'` is false,
or the left half if `c f'` is true.
Then we simplify the expression using `find-or-last-config-with` and recurse in
case `f ≢ f'`.
-}
conf'-lemma : ∀ (c : FST.Configuration F) (f : F) (fs : List F)
  → f ∈ fs
    ----------------------------------------------
  → find-or-last (conf' c fs) (configs fs) f ≡ c f
conf'-lemma c f (f' ∷ fs) f∈fs with f ==ꟳ f'
conf'-lemma c f (.f ∷ fs) f∈fs | yes refl with c f
conf'-lemma c f (.f ∷ fs) f∈fs | yes refl | true =
    find-or-last (List⁺.length (configs fs) + conf' c fs) (configs (f ∷ fs)) f
  ≡⟨⟩
    find-or-last (List⁺.length (configs fs) + conf' c fs) (List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)) f
  ≡⟨ Eq.cong-app (Eq.cong₂ find-or-last {u = List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)} (Eq.cong₂ _+_ (List⁺.length-map (config-with false f) (configs fs)) refl) refl) f ⟨
    find-or-last (List⁺.length (List⁺.map (config-with false f) (configs fs)) + conf' c fs) (List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)) f
  ≡⟨ Eq.cong-app (find-or-last-prepend-+ (conf' c fs) (List⁺.map (config-with false f) (configs fs)) (List⁺.map (config-with true f) (configs fs))) f ⟩
    find-or-last (conf' c fs) (List⁺.map (config-with true f) (configs fs)) f
  ≡⟨ find-or-last-config-with c true f f fs (λ c → true) (λ c → config-with-≡ true f c) ⟩
    true
  ∎
  where
  open Eq.≡-Reasoning
conf'-lemma c f (.f ∷ fs) f∈fs | yes refl | false =
    find-or-last (conf' c fs) (configs (f ∷ fs)) f
  ≡⟨⟩
    find-or-last (conf' c fs) (List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)) f
  ≡⟨ Eq.cong-app (find-or-last-append (List⁺.map (config-with false f) (configs fs)) (List⁺.map (config-with true f) (configs fs)) (ℕ.≤-trans (conf'<configs c fs) (ℕ.≤-reflexive (Eq.sym (List⁺.length-map (config-with false f) (configs fs)))))) f ⟩
    find-or-last (conf' c fs) (List⁺.map (config-with false f) (configs fs)) f
  ≡⟨ find-or-last-config-with c false f f fs (λ c → false) (λ c → config-with-≡ false f c) ⟩
    false
  ∎
  where
  open Eq.≡-Reasoning
conf'-lemma c f (f' ∷ fs) (here f≡f') | no f≢f' = ⊥-elim (f≢f' f≡f')
conf'-lemma c f (f' ∷ fs) (there f∈fs) | no f≢f' with c f'
conf'-lemma c f (f' ∷ fs) (there f∈fs) | no f≢f' | true =
    find-or-last (List⁺.length (configs fs) + conf' c fs) (configs (f' ∷ fs)) f
  ≡⟨⟩
    find-or-last (List⁺.length (configs fs) + conf' c fs) (List⁺.map (config-with false f') (configs fs) ⁺++⁺ List⁺.map (config-with true f') (configs fs)) f
  ≡⟨ Eq.cong-app (Eq.cong₂ find-or-last {u = List⁺.map (config-with false f') (configs fs) ⁺++⁺ List⁺.map (config-with true f') (configs fs)} (Eq.cong₂ _+_ (List⁺.length-map (config-with false f') (configs fs)) refl) refl) f ⟨
    find-or-last (List⁺.length (List⁺.map (config-with false f') (configs fs)) + conf' c fs) (List⁺.map (config-with false f') (configs fs) ⁺++⁺ List⁺.map (config-with true f') (configs fs)) f
  ≡⟨ Eq.cong-app (find-or-last-prepend-+ (conf' c fs) (List⁺.map (config-with false f') (configs fs)) (List⁺.map (config-with true f') (configs fs))) f ⟩
    find-or-last (conf' c fs) (List⁺.map (config-with true f') (configs fs)) f
  ≡⟨ find-or-last-config-with c true f f' fs (λ c → c f) (λ c → config-with-≢ true f f' f≢f' c) ⟩
    find-or-last (conf' c fs) (configs fs) f
  ≡⟨ conf'-lemma c f fs f∈fs ⟩
    c f
  ∎
  where
  open Eq.≡-Reasoning
conf'-lemma c f (f' ∷ fs) (there f∈fs) | no f≢f' | false =
    find-or-last (conf' c fs) (configs (f' ∷ fs)) f
  ≡⟨⟩
    find-or-last (conf' c fs) (List⁺.map (config-with false f') (configs fs) ⁺++⁺ List⁺.map (config-with true f') (configs fs)) f
  ≡⟨ Eq.cong-app (find-or-last-append (List⁺.map (config-with false f') (configs fs)) (List⁺.map (config-with true f') (configs fs)) ((ℕ.≤-trans (conf'<configs c fs) (ℕ.≤-reflexive (Eq.sym (List⁺.length-map (config-with false f') (configs fs))))))) f ⟩
    find-or-last (conf' c fs) (List⁺.map (config-with false f') (configs fs)) f
  ≡⟨ find-or-last-config-with c false f f' fs (λ c → c f) (λ c → config-with-≢ false f f' f≢f' c) ⟩
    find-or-last (conf' c fs) (configs fs) f
  ≡⟨ conf'-lemma c f fs f∈fs ⟩
    c f
  ∎
  where
  open Eq.≡-Reasoning

{-|
If we can prove a predicate `P a`,
given a proof that `a` is an element of a list `as`,
we can prove the predicate for all elements of that list `as`.
-}
AllWith∈ : ∀ {A : Set} {P : A → Set} (as : List A) → ((a : A) → a ∈ as → P a) → All P as
AllWith∈ [] f = []
AllWith∈ (a ∷ as) f = f a (here refl) ∷ AllWith∈ as (λ a a∈as → f a (there a∈as))

{-|
If two configurations agree on their value for all features in an FST,
then the semantics must also agree.
This looks like functional extensionality from the perspective of the semantics (`FST.⟦_⟧`)
because it does not observe values other than `map name fs`.
In fact, this theorem states that (extensionally) equal configurations are
indistinguishable in semantics and hence produce the same result.
The proof works by showing that both configurations select the same list of features (in the same order)
from the list of available features in the input SPL.
-}
⟦⟧-cong : ∀ {A : 𝔸} (a : atoms A) (fs : List (Feature F A))
  → (c₁ c₂ : FST.Configuration F)
  → All (λ f → c₁ f ≡ c₂ f) (map name fs)
  → FST.⟦ a ◀ fs ⟧ c₁ ≡ FST.⟦ a ◀ fs ⟧ c₂
⟦⟧-cong {A} a fs c₁ c₂ ps = Eq.cong₂ _-<_>- refl (Eq.cong forget-uniqueness (Eq.cong ⊛-all (go fs ps)))
  where
  go : (fs : List (Feature F A))
    → All (λ f → c₁ f ≡ c₂ f) (map name fs)
    → select c₁ fs ≡ select c₂ fs
  go [] p = refl
  go ((f :: i) ∷ fs) (px ∷ p) with c₁ f | c₂ f
  go ((f :: i) ∷ fs) (px ∷ p) | false | false = go fs p
  go ((f :: i) ∷ fs) (px ∷ p) | true  | true = Eq.cong₂ _∷_ refl (go fs p)

preserves-⊆ : ∀ {A : 𝔸} → (e : SPL F A) → VariantList.⟦ translate e ⟧ ⊆[ fnoc e ] FST.⟦ e ⟧
preserves-⊆ e@(a ◀ fs) c =
    VariantList.⟦ translate e ⟧ c
  ≡⟨⟩
    find-or-last c (translate e)
  ≡⟨⟩
    find-or-last c (List⁺.map (λ c → FST.⟦ e ⟧ c) (configs (map name fs)))
  ≡⟨ map-find-or-last (λ c → FST.⟦ e ⟧ c) c (configs (map name fs)) ⟨
    FST.⟦ e ⟧ (find-or-last c (configs (map name fs)))
  ≡⟨⟩
    FST.⟦ e ⟧ (fnoc e c)
  ∎
  where
  open Eq.≡-Reasoning

preserves-⊇ : ∀ {A : 𝔸} → (e : SPL F A) → FST.⟦ e ⟧ ⊆[ conf e ] VariantList.⟦ translate e ⟧
preserves-⊇ e@(a ◀ fs) c =
    FST.⟦ e ⟧ c
  ≡⟨ ⟦⟧-cong a fs c (find-or-last (conf e c) (configs (map name fs))) (AllWith∈ (map name fs) (λ f f∈fs → Eq.sym (conf'-lemma c f (map name fs) f∈fs))) ⟩
    FST.⟦ e ⟧ (find-or-last (conf e c) (configs (map name fs)))
  ≡⟨ map-find-or-last (λ c → FST.⟦ e ⟧ c) (conf e c) (configs (map name fs)) ⟩
    find-or-last (conf e c) (List⁺.map (λ c → FST.⟦ e ⟧ c) (configs (map name fs)))
  ≡⟨⟩
    find-or-last (conf e c) (translate e)
  ≡⟨⟩
    VariantList.⟦ translate e ⟧ (conf e c)
  ∎
  where
  open Eq.≡-Reasoning

preserves : ∀ {A : 𝔸} → (e : SPL F A) → VariantList.⟦ translate e ⟧ ≅[ fnoc e ][ conf e ] FST.⟦ e ⟧
preserves e = preserves-⊆ e , preserves-⊇ e

FST→VariantList : LanguageCompiler (FSTL F) VariantListL
FST→VariantList .LanguageCompiler.compile = translate
FST→VariantList .LanguageCompiler.config-compiler expr .to = conf expr
FST→VariantList .LanguageCompiler.config-compiler expr .from = fnoc expr
FST→VariantList .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

VariantList≽FST : VariantListL ≽ FSTL F
VariantList≽FST = expressiveness-from-compiler FST→VariantList