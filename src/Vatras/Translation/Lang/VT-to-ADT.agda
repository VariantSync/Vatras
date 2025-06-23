open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; cong; cong₂)
import Relation.Binary.Structures
open Relation.Binary.Structures.IsPreorder ℕ.≤-isPreorder using () renaming (≲-respʳ-≈ to ℕ-≤-≡ʳ; ≲-respˡ-≈ to ℕ-≤-≡ˡ)

import Vatras.Util.ProxyInduction as ProxyInduction
open import Vatras.Data.Prop using (Prop; eval)
open import Vatras.Data.EqIndexedSet using (≗→≅[])
open import Vatras.Framework.Variants using (Forest; _-<_>-)
open import Vatras.Framework.Compiler as Compiler using (LanguageCompiler)
import Vatras.Lang.ADT
open Vatras.Lang.ADT (Prop F) Forest using (ADT; leaf; _⟨_,_⟩)
open Vatras.Lang.ADT       F  Forest using (ADTL)
open import Vatras.Lang.VT F as VT using (VT; UnrootedVT; VTL; ⟦_⟧; _-<_>-; if-true[_]; if[_]then[_]; if[_]then[_]else[_]; vt-leaf; configure; configure-all)

open import Vatras.Lang.ADT.Prop F Forest using (⟦_⟧ₚ; PropADTL)

open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_; ≽-trans; expressiveness-from-compiler)
open import Vatras.Translation.Lang.ADT.PropSemantics F Forest using (formula-elim-compiler; PropADT≽ADT)

module _ {A : 𝔸} where
  -- induction proxy
  sizeVTs : List (UnrootedVT A) → ℕ
  sizeVTs [] = zero
  sizeVTs ((a -< l >-) ∷ xs) = suc (sizeVTs l) + sizeVTs xs
  sizeVTs (if[ p ]then[ l ] ∷ xs) = suc (sizeVTs l) + sizeVTs xs
  sizeVTs (if[ p ]then[ l ]else[ r ] ∷ xs) = suc (sizeVTs l) + sizeVTs r + sizeVTs xs

  -- lemmas used to prove termination
  sizeVTs-++ : ∀ xs ys → sizeVTs (xs ++ ys) ≡ sizeVTs xs + sizeVTs ys
  sizeVTs-++ [] ys = refl
  sizeVTs-++ ((a -< l >-) ∷ xs) ys = Eq.cong suc (Eq.trans (Eq.cong (sizeVTs l +_) (sizeVTs-++ xs ys)) (Eq.sym (ℕ.+-assoc (sizeVTs l) (sizeVTs xs) (sizeVTs ys))))
  sizeVTs-++ (if[ p ]then[ l ] ∷ xs) ys = Eq.cong suc (Eq.trans (Eq.cong (sizeVTs l +_) (sizeVTs-++ xs ys)) (Eq.sym (ℕ.+-assoc (sizeVTs l) (sizeVTs xs) (sizeVTs ys))))
  sizeVTs-++ (if[ p ]then[ l ]else[ r ] ∷ xs) ys = Eq.cong suc (Eq.trans (Eq.cong (sizeVTs l + sizeVTs r +_) (sizeVTs-++ xs ys)) (Eq.sym (ℕ.+-assoc (sizeVTs l + sizeVTs r) (sizeVTs xs) (sizeVTs ys))))

  _<ₛ_ : List (UnrootedVT A) → List (UnrootedVT A) → Set
  _<ₛ_ vt₁ vt₂ = sizeVTs vt₁ < sizeVTs vt₂

  <ₛ-artifact : ∀ a l xs → l <ₛ ((a -< l >-) ∷ xs)
  <ₛ-artifact a l xs = s≤s (ℕ.m≤m+n (sizeVTs l) (sizeVTs xs))

  <ₛ-tail : ∀ x xs → xs <ₛ (x ∷ xs)
  <ₛ-tail (a -< l >-) xs = s≤s (ℕ.m≤n+m (sizeVTs xs) (sizeVTs l))
  <ₛ-tail if[ p ]then[ l ] xs = s≤s (ℕ.m≤n+m (sizeVTs xs) (sizeVTs l))
  <ₛ-tail if[ p ]then[ l ]else[ r ] xs = s≤s (ℕ.m≤n+m (sizeVTs xs) (sizeVTs l + sizeVTs r))

  <ₛ-if : ∀ p l xs → (l ++ xs) <ₛ (if[ p ]then[ l ] ∷ xs)
  <ₛ-if p l xs = s≤s (ℕ.≤-reflexive (sizeVTs-++ l xs))

  <ₛ-if-then₁ : ∀ p l r xs → (l ++ xs) <ₛ (if[ p ]then[ l ]else[ r ] ∷ xs)
  <ₛ-if-then₁ p l r xs = s≤s (ℕ-≤-≡ˡ (Eq.sym (sizeVTs-++ l xs)) (ℕ.+-monoˡ-≤ (sizeVTs xs) (ℕ.m≤m+n (sizeVTs l) (sizeVTs r))))

  <ₛ-if-then₂ : ∀ p l r xs → (r ++ xs) <ₛ (if[ p ]then[ l ]else[ r ] ∷ xs)
  <ₛ-if-then₂ p l r xs = s≤s (ℕ-≤-≡ˡ (Eq.sym (sizeVTs-++ r xs)) (ℕ-≤-≡ʳ (Eq.sym (ℕ.+-assoc (sizeVTs l) (sizeVTs r) (sizeVTs xs))) (ℕ.m≤n+m (sizeVTs r + sizeVTs xs) (sizeVTs l))))

  -- artifact atom, artifact children, artifact neighbors
  pushy : atoms A → ADT A → ADT A → ADT A
  pushy a (leaf v)      (leaf v')     = leaf (a -< v >- ∷ v')
  pushy a c@(leaf v)    (D ⟨ l , r ⟩) = D ⟨ pushy a c l , pushy a c r ⟩
  pushy a (D ⟨ l , r ⟩) n             = D ⟨ pushy a l n , pushy a r n ⟩

  translate-all-step : ∀ (vts : List (UnrootedVT A)) → (∀ vts' → sizeVTs vts' < sizeVTs vts → ADT A) → ADT A
  translate-all-step [] rec = leaf []
  translate-all-step ((a -< l >-) ∷ xs) rec = pushy a (rec l (<ₛ-artifact a l xs)) (rec xs (<ₛ-tail (a -< l >-) xs))
  translate-all-step (if[ p ]then[ l ] ∷ xs) rec = p ⟨ rec (l ++ xs) (<ₛ-if p l xs) , rec xs (<ₛ-tail (if[ p ]then[ l ]) xs) ⟩
  translate-all-step (if[ p ]then[ l ]else[ r ] ∷ xs) rec = p ⟨ rec (l ++ xs) (<ₛ-if-then₁ p l r xs) , rec (r ++ xs) (<ₛ-if-then₂ p l r xs) ⟩

  translate-all : List (UnrootedVT A) → ADT A
  translate-all = ProxyInduction.induction sizeVTs (λ _ → ADT A) translate-all-step

  translate-all-step' : ∀ vts → translate-all vts ≡ translate-all-step vts (λ vts _ → translate-all vts)
  translate-all-step' = induction-step translate-all-step go
    where
    open ProxyInduction sizeVTs (λ _ → ADT A)

    go : RecIrrelevant translate-all-step
    go [] ext = refl
    go ((a -< l >-) ∷ vts) ext = Eq.cong₂ (pushy a) (ext l (<ₛ-artifact a l vts)) (ext vts (s≤s (ℕ.m≤n+m (sizeVTs vts) (sizeVTs l))))
    go (if[ p ]then[ l ] ∷ vts) ext = Eq.cong₂ (p ⟨_,_⟩) (ext (l ++ vts) (<ₛ-if p l vts)) (ext vts (s≤s (ℕ.m≤n+m (sizeVTs vts) (sizeVTs l))))
    go (if[ p ]then[ l ]else[ r ] ∷ vts) ext = Eq.cong₂ (p ⟨_,_⟩) (ext (l ++ vts) (<ₛ-if-then₁ p l r vts)) (ext (r ++ vts) (<ₛ-if-then₂ p l r vts))

  translate : VT A → ADT A
  translate if-true[ xs ] = translate-all xs

  -- Preservation Proofs --

  -- formal specification of pushy: It should create an ADT such that for any configuration c, there is an artifact at the top of left
  pushy-preserves : ∀ a l n c → ⟦ pushy a l n ⟧ₚ c ≡ a -< ⟦ l ⟧ₚ c >- ∷ ⟦ n ⟧ₚ c
  pushy-preserves a (leaf v) (leaf v') c = refl
  pushy-preserves a (D ⟨ l , r ⟩) n c with eval D c
  ... | true  = pushy-preserves a l n c
  ... | false = pushy-preserves a r n c
  pushy-preserves a x@(leaf v) (D ⟨ l , r ⟩) c with eval D c
  ... | true  = pushy-preserves a x l c
  ... | false = pushy-preserves a x r c

  ++-preserves : ∀ l r c → ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c ≡ ⟦ translate-all (l ++ r) ⟧ₚ c
  ++-preserves l r c = induction step l
    where
    open ProxyInduction sizeVTs (λ l → ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c ≡ ⟦ translate-all (l ++ r) ⟧ₚ c)

    step : Step
    step [] rec = refl
    step ((a -< l >-) ∷ ls) rec =
        ⟦ translate-all ((a -< l >-) ∷ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c) (translate-all-step' ((a -< l >-) ∷ ls)) ⟩
        ⟦ pushy a (translate-all l) (translate-all ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Eq.cong (_++ ⟦ translate-all r ⟧ₚ c) (pushy-preserves a (translate-all l) (translate-all ls) c) ⟩
        a -< ⟦ translate-all l ⟧ₚ c >- ∷ ⟦ translate-all ls ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Eq.cong (a -< ⟦ translate-all l ⟧ₚ c >- ∷_) (rec ls term₁) ⟩
        a -< ⟦ translate-all l ⟧ₚ c >- ∷ ⟦ translate-all (ls ++ r) ⟧ₚ c
      ≡⟨ pushy-preserves a (translate-all l) (translate-all (ls ++ r)) c ⟨
        ⟦ pushy a (translate-all l) (translate-all (ls ++ r)) ⟧ₚ c
      ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' (((a -< l >-) ∷ ls) ++ r)) ⟨
        ⟦ translate-all (((a -< l >-) ∷ ls) ++ r) ⟧ₚ c
      ∎
      where
      open Eq.≡-Reasoning

      term₁ : sizeVTs ls < suc (sizeVTs l + sizeVTs ls)
      term₁ = (s≤s (ℕ.m≤n+m (sizeVTs ls) (sizeVTs l)))
    step (if[ p ]then[ l₁ ] ∷ ls) rec =
        ⟦ translate-all (if[ p ]then[ l₁ ] ∷ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c) (translate-all-step' (if[ p ]then[ l₁ ] ∷ ls)) ⟩
        ⟦ p ⟨ translate-all (l₁ ++ ls) , translate-all ls ⟩ ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls) ⟧ₚ c else ⟦ translate-all ls ⟧ₚ c) ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Bool.if-float (_++ ⟦ translate-all r ⟧ₚ c) (eval p c) ⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c else ⟦ translate-all ls ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c)
      ≡⟨ Eq.cong₂ (if eval p c then_else_) (rec (l₁ ++ ls) term₁) (rec ls term₂) ⟩
        (if eval p c then ⟦ translate-all ((l₁ ++ ls) ++ r) ⟧ₚ c else ⟦ translate-all (ls ++ r) ⟧ₚ c)
      ≡⟨ Eq.cong (λ x → (if eval p c then ⟦ translate-all x ⟧ₚ c else ⟦ translate-all (ls ++ r) ⟧ₚ c)) (++-assoc l₁ ls r) ⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls ++ r) ⟧ₚ c else ⟦ translate-all (ls ++ r) ⟧ₚ c)
      ≡⟨⟩
        ⟦ p ⟨ translate-all (l₁ ++ ls ++ r) , translate-all (ls ++ r) ⟩ ⟧ₚ c
      ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' (if[ p ]then[ l₁ ] ∷ ls ++ r)) ⟨
        ⟦ translate-all (if[ p ]then[ l₁ ] ∷ ls ++ r) ⟧ₚ c
      ∎
      where
      open Eq.≡-Reasoning

      term₁ : sizeVTs (l₁ ++ ls) < suc (sizeVTs l₁ + sizeVTs ls)
      term₁ = (s≤s (ℕ.≤-reflexive (sizeVTs-++ l₁ ls)))

      term₂ : sizeVTs ls < suc (sizeVTs l₁ + sizeVTs ls)
      term₂ = (s≤s (ℕ.m≤n+m (sizeVTs ls) (sizeVTs l₁)))
    step (if[ p ]then[ l₁ ]else[ r₁ ] ∷ ls) rec =
        ⟦ translate-all (if[ p ]then[ l₁ ]else[ r₁ ] ∷ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ cong (λ x → ⟦ x ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c) (translate-all-step' (if[ p ]then[ l₁ ]else[ r₁ ] ∷ ls)) ⟩
        ⟦ p ⟨ translate-all (l₁ ++ ls) , translate-all (r₁ ++ ls) ⟩ ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls) ⟧ₚ c else ⟦ translate-all (r₁ ++ ls) ⟧ₚ c) ++ ⟦ translate-all r ⟧ₚ c
      ≡⟨ Bool.if-float (_++ ⟦ translate-all r ⟧ₚ c) (eval p c) ⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c else ⟦ translate-all (r₁ ++ ls) ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c)
      ≡⟨ Eq.cong₂ (if eval p c then_else_) (rec (l₁ ++ ls) term₁) (rec (r₁ ++ ls) term₂) ⟩
        (if eval p c then ⟦ translate-all ((l₁ ++ ls) ++ r) ⟧ₚ c else ⟦ translate-all ((r₁ ++ ls) ++ r) ⟧ₚ c)
      ≡⟨ cong₂ (λ x y → if eval p c then ⟦ translate-all x ⟧ₚ c else ⟦ translate-all y ⟧ₚ c) (++-assoc l₁ ls r) (++-assoc r₁ ls r) ⟩
        (if eval p c then ⟦ translate-all (l₁ ++ ls ++ r) ⟧ₚ c else ⟦ translate-all (r₁ ++ ls ++ r) ⟧ₚ c)
      ≡⟨⟩
        ⟦ p ⟨ translate-all (l₁ ++ ls ++ r) , translate-all (r₁ ++ ls ++ r) ⟩ ⟧ₚ c
      ≡⟨ cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' (if[ p ]then[ l₁ ]else[ r₁ ] ∷ ls ++ r)) ⟨
        ⟦ translate-all (if[ p ]then[ l₁ ]else[ r₁ ] ∷ ls ++ r) ⟧ₚ c
      ∎
      where
      open Eq.≡-Reasoning

      term₁ : sizeVTs (l₁ ++ ls) < suc (sizeVTs l₁ + sizeVTs r₁ + sizeVTs ls)
      term₁ = s≤s (ℕ.≤-trans (ℕ.≤-reflexive (sizeVTs-++ l₁ ls)) (ℕ.+-monoˡ-≤ (sizeVTs ls) (ℕ.m≤m+n (sizeVTs l₁) (sizeVTs r₁))))

      term₂ : sizeVTs (r₁ ++ ls) < suc (sizeVTs l₁ + sizeVTs r₁ + sizeVTs ls)
      term₂ = s≤s (ℕ.≤-trans (ℕ.≤-reflexive (sizeVTs-++ r₁ ls)) (ℕ.+-monoˡ-≤ (sizeVTs ls) (ℕ.m≤n+m (sizeVTs r₁) (sizeVTs l₁))))

  preserves-all : ∀ (vts : List (UnrootedVT A)) → configure-all vts ≗ ⟦ translate-all vts ⟧ₚ
  preserves-all [] c = refl
  preserves-all ((a -< l >-) ∷ xs) c =
      configure-all ((a -< l >-) ∷ xs) c
    ≡⟨⟩
      a -< configure-all l c >- ∷ configure-all xs c
    ≡⟨ Eq.cong₂ (λ x y → a -< x >- ∷ y) (preserves-all l c) (preserves-all xs c) ⟩
      a -< ⟦ translate-all l ⟧ₚ c >- ∷ ⟦ translate-all xs ⟧ₚ c
    ≡⟨ pushy-preserves a (translate-all l) (translate-all xs) c ⟨
      ⟦ pushy a (translate-all l) (translate-all xs) ⟧ₚ c
    ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' ((a -< l >-) ∷ xs)) ⟨
      ⟦ translate-all ((a -< l >-) ∷ xs) ⟧ₚ c
    ∎
    where
    open Eq.≡-Reasoning
  preserves-all (if[ p ]then[ l ] ∷ xs) c =
      configure-all (if[ p ]then[ l ] ∷ xs) c
    ≡⟨⟩
      (if eval p c then configure-all l c else []) ++ configure-all xs c
    ≡⟨ Bool.if-float (_++ configure-all xs c) (eval p c) ⟩
      (if eval p c then configure-all l c ++ configure-all xs c else configure-all xs c)
    ≡⟨ Eq.cong₂ (if eval p c then_else_) (Eq.cong₂ _++_ (preserves-all l c) (preserves-all xs c)) (preserves-all xs c) ⟩
      (if eval p c then ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c else ⟦ translate-all xs ⟧ₚ c)
    ≡⟨ Eq.cong (if eval p c then_else ⟦ translate-all xs ⟧ₚ c) (++-preserves l xs c) ⟩
      (if eval p c then ⟦ translate-all (l ++ xs) ⟧ₚ c else ⟦ translate-all xs ⟧ₚ c)
    ≡⟨⟩
      ⟦ p ⟨ translate-all (l ++ xs) , translate-all xs ⟩ ⟧ₚ c
    ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' (if[ p ]then[ l ] ∷ xs)) ⟨
      ⟦ translate-all (if[ p ]then[ l ] ∷ xs) ⟧ₚ c
    ∎
    where
    open Eq.≡-Reasoning
  preserves-all (if[ p ]then[ l ]else[ r ] ∷ xs) c =
      configure-all (if[ p ]then[ l ]else[ r ] ∷ xs) c
    ≡⟨⟩
      (if eval p c then configure-all l c else configure-all r c) ++ configure-all xs c
    ≡⟨ Bool.if-float (_++ configure-all xs c) (eval p c) ⟩
      (if eval p c then configure-all l c ++ configure-all xs c else configure-all r c ++ configure-all xs c)
    ≡⟨ Eq.cong₂ (if eval p c then_else_) (Eq.cong₂ _++_ (preserves-all l c) (preserves-all xs c)) (Eq.cong₂ _++_ (preserves-all r c) (preserves-all xs c)) ⟩
      (if eval p c then ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c else ⟦ translate-all r ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c)
    ≡⟨ Eq.cong₂ (if eval p c then_else_) (++-preserves l xs c) (++-preserves r xs c) ⟩
      (if eval p c then ⟦ translate-all (l ++ xs) ⟧ₚ c else ⟦ translate-all (r ++ xs) ⟧ₚ c)
    ≡⟨⟩
      ⟦ p ⟨ translate-all (l ++ xs) , translate-all (r ++ xs) ⟩ ⟧ₚ c
    ≡⟨ Eq.cong (λ x → ⟦ x ⟧ₚ c) (translate-all-step' (if[ p ]then[ l ]else[ r ] ∷ xs)) ⟨
      ⟦ translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) ⟧ₚ c
    ∎
    where
    open Eq.≡-Reasoning

  preserves : ∀ (vt : VT A) → ⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
  preserves if-true[ xs ] c = preserves-all xs c

VT→PropADT : LanguageCompiler VTL PropADTL
VT→PropADT = record
  { compile = translate
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = ≗→≅[] ∘ preserves
  }

PropADT≽VT : PropADTL ≽ VTL
PropADT≽VT = expressiveness-from-compiler VT→PropADT

VT→ADT : LanguageCompiler VTL ADTL
VT→ADT = VT→PropADT Compiler.⊕ formula-elim-compiler

ADT≽VT : ADTL ≽ VTL
ADT≽VT = ≽-trans PropADT≽ADT PropADT≽VT

{-|
This module contains some tests for the translation function to see it in action.
-}
module Test {A : 𝔸} where
  open Vatras.Framework.Variants using (rose-leaf; forest-leaf; forest-singleton)

  module Forest (a b : atoms A) where
    vt : VT A
    vt =
      if-true[
        vt-leaf a ∷ vt-leaf b ∷ []
      ]

    adt : ADT A
    adt = leaf (rose-leaf a ∷ rose-leaf b ∷ [])

    tr : translate vt ≡ adt
    tr = refl

    pres : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres _ = refl

  module SingleOption (X : Prop F) (a b : atoms A) where
    vt : VT A
    vt =
      if-true[
        a -<
          if[ X ]then[
            vt-leaf b ∷ []
          ] ∷ []
        >- ∷ []
      ]

    adt : ADT A
    adt = X ⟨ leaf (forest-singleton a (forest-leaf b)) , leaf (forest-leaf a) ⟩

    tr : translate vt ≡ adt
    tr = refl

    pres-t : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres-t c with eval X c
    ... | true  = refl
    ... | false = refl

  module SingleChoice (X : Prop F) (a b₁ b₂ e₁ e₂ : atoms A) where
    vt : VT A
    vt =
      if-true[
        a -<
          if[ X ]then[
            vt-leaf b₁ ∷
            vt-leaf b₂ ∷ []
          ]else[
            vt-leaf e₁ ∷
            vt-leaf e₂ ∷ []
          ] ∷ []
        >- ∷ []
      ]

    adt : ADT A
    adt =
      X ⟨
        leaf (forest-singleton a (rose-leaf b₁ ∷ rose-leaf b₂ ∷ [])) ,
        leaf (forest-singleton a (rose-leaf e₁ ∷ rose-leaf e₂ ∷ []))
      ⟩

    tr : translate vt ≡ adt
    tr = refl

    pres-t : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres-t c with eval X c
    ... | true  = refl
    ... | false = refl
