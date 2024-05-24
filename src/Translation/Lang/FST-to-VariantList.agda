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

configs : List F → List⁺ (FST.Configuration F)
configs [] = (λ _ → false) ∷ []
configs (f ∷ fs) = List⁺.map (config-with false f) (configs fs) ⁺++⁺ List⁺.map (config-with true f) (configs fs)

translate : ∀ {A : 𝔸} → SPL F A → VariantList A
translate {A} (a ◀ fs) = List⁺.map (λ c → FST.⟦ a ◀ fs ⟧ c) (configs (map name fs))

conf' : FST.Configuration F → List F → ℕ
conf' c [] = 0
conf' c (f ∷ fs) with c f
conf' c (f ∷ fs) | true = List⁺.length (configs fs) + conf' c fs
conf' c (f ∷ fs) | false = conf' c fs

conf : ∀ {A : 𝔸} → (e : SPL F A) → FST.Configuration F → VariantList.Configuration
conf {A} (_ ◀ fs) c = conf' c (map name fs)

fnoc : ∀ {A : 𝔸} → (e : SPL F A) → VariantList.Configuration → FST.Configuration F
fnoc {A} (_ ◀ fs) n f = find-or-last n (configs (map name fs)) f

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

config-with-≡ : (b : Bool) → (f : F) → (c : FST.Configuration F) → config-with b f c f ≡ b
config-with-≡ b f c with f ==ꟳ f
config-with-≡ b f c | no f≢f = ⊥-elim (f≢f refl)
config-with-≡ b f c | yes _ = refl

config-with-≢ : (b : Bool) → (f f' : F) → f ≢ f' → (c : FST.Configuration F) → config-with b f' c f ≡ c f
config-with-≢ b f f' f≢f' c with f' ==ꟳ f
config-with-≢ b f f' f≢f' c | no _ = refl
config-with-≢ b f f' f≢f' c | yes f'≡f = ⊥-elim (f≢f' (Eq.sym f'≡f))

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

conf'-lemma : (c : FST.Configuration F) → (f : F) → (fs : List F) → f ∈ fs → find-or-last (conf' c fs) (configs fs) f ≡ c f
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

AllWith∈ : ∀ {A : Set} {P : A → Set} (as : List A) → ((a : A) → a ∈ as → P a) → All P as
AllWith∈ [] f = []
AllWith∈ (a ∷ as) f = f a (here refl) ∷ AllWith∈ as (λ a a∈as → f a (there a∈as))

⟦⟧-cong : ∀ {A : 𝔸} (a : atoms A) (fs : List (Feature F A)) (c : FST.Configuration F)
  → (g : FST.Configuration F → FST.Configuration F)
  → All (λ f → g c f ≡ c f) (map name fs)
  → FST.⟦ a ◀ fs ⟧ (g c) ≡ FST.⟦ a ◀ fs ⟧ c
⟦⟧-cong {A} a fs c g ps = Eq.cong₂ _-<_>- refl (Eq.cong forget-uniqueness (Eq.cong ⊛-all (go fs ps)))
  where
  go : (fs : List (Feature F A))
    → All (λ f → g c f ≡ c f) (map name fs)
    → select (g c) fs ≡ select c fs
  go [] p = refl
  go ((f :: i) ∷ fs) (px ∷ p) with (g c) f | c f
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
  ≡⟨ ⟦⟧-cong a fs c (λ c → find-or-last (conf e c) (configs (map name fs))) (AllWith∈ (map name fs) (λ f f∈fs → conf'-lemma c f (map name fs) f∈fs)) ⟨
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
