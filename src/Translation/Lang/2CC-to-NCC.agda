{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.2CC-to-NCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.Fin using (zero; suc)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Nat using (zero)
open import Data.Product using () renaming (_,_ to _and_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (Size)
open import Util.Nat.AtLeast using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

import Lang.NCC
module NCC where
  open Lang.NCC public
  module NCC-Sem-1 n D = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-1 using (NCCL) public
  module NCC-Sem-2 {n} {D} = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-2 using (⟦_⟧) public
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

import Lang.2CC
module 2CC where
  open Lang.2CC public
  module 2CC-Sem-1 D = Lang.2CC.Sem D Variant Artifact∈ₛVariant
  open 2CC-Sem-1 using (2CCL) public
  module 2CC-Sem-2 {D} = Lang.2CC.Sem D Variant Artifact∈ₛVariant
  open 2CC-Sem-2 using (⟦_⟧) public
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩)

import Translation.Lang.NCC-to-NCC
open Translation.Lang.NCC-to-NCC.IncreaseArity Variant Artifact∈ₛVariant using (NCC→NCC)

artifact : ∀ {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module 2Ary where
  translate : ∀ {i : Size} {D A : Set}
    → 2CC D i A
    → NCC (sucs zero) D i A
  translate (a -< cs >-) = a -< List.map translate cs >-
  translate (d ⟨ l , r ⟩) = d ⟨ translate l ∷ translate r ∷ [] ⟩

  conf : ∀ {D : Set} → 2CC.Configuration D → NCC.Configuration (sucs zero) D
  conf config d with config d
  ... | true = zero
  ... | false = suc zero

  fnoc : ∀ {D : Set} → NCC.Configuration (sucs zero) D → 2CC.Configuration D
  fnoc config d with config d
  ... | zero = true
  ... | suc zero = false

  preserves-⊆ : ∀ {i : Size} {D A : Set}
    → (expr : 2CC D i A)
    → NCC.⟦ translate expr ⟧ ⊆[ fnoc ] 2CC.⟦ expr ⟧
  preserves-⊆ (a -< cs >-) config =
      NCC.⟦ translate (a -< cs >-) ⟧ config
    ≡⟨⟩
      NCC.⟦ a -< List.map translate cs >- ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → NCC.⟦ e ⟧ config) (List.map translate cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → NCC.⟦ translate e ⟧ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
      artifact a (List.map (λ e → 2CC.⟦ e ⟧ (fnoc config)) cs)
    ≡⟨⟩
      2CC.⟦ a -< cs >- ⟧ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l , r ⟩) config =
      NCC.⟦ translate (d ⟨ l , r ⟩) ⟧ config
    ≡⟨⟩
      NCC.⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (translate l ∷ translate r ∷ []) (config d) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config d) translate (l ∷ r ∷ [])) refl ⟩
      NCC.⟦ translate (Vec.lookup (l ∷ r ∷ []) (config d)) ⟧ config
    ≡⟨ preserves-⊆ (Vec.lookup (l ∷ r ∷ []) (config d)) config ⟩
      2CC.⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧ (fnoc config)
    ≡⟨ Eq.cong₂ 2CC.⟦_⟧ lemma refl ⟩
      2CC.⟦ if (fnoc config d) then l else r ⟧ (fnoc config)
    ≡⟨⟩
      2CC.⟦ d ⟨ l , r ⟩ ⟧ (fnoc config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if fnoc config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves-⊇ : ∀ {i : Size} {D A : Set}
    → (expr : 2CC D i A)
    → 2CC.⟦ expr ⟧ ⊆[ conf ] NCC.⟦ translate expr ⟧
  preserves-⊇ (a -< cs >-) config =
      2CC.⟦ a -< cs >- ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → 2CC.⟦ e ⟧ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
      artifact a (List.map (λ e → NCC.⟦ translate e ⟧ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → NCC.⟦ e ⟧ (conf config)) (List.map translate cs))
    ≡⟨⟩
      NCC.⟦ a -< List.map translate cs >- ⟧ (conf config)
    ≡⟨⟩
      NCC.⟦ translate (a -< cs >-) ⟧ (conf config)
    ∎
  preserves-⊇ (d ⟨ l , r ⟩) config =
      2CC.⟦ d ⟨ l , r ⟩ ⟧ config
    ≡⟨⟩
      2CC.⟦ if config d then l else r ⟧ config
    ≡⟨⟩
      2CC.⟦ if config d then l else r ⟧ config
    ≡⟨ preserves-⊇ (if config d then l else r) config ⟩
      NCC.⟦ translate (if config d then l else r) ⟧ (conf config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Bool.push-function-into-if (translate) (config d)) refl ⟩
      NCC.⟦ if config d then translate l else translate r ⟧ (conf config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ lemma refl ⟩
      NCC.⟦ Vec.lookup (translate l ∷ translate r ∷ []) (conf config d) ⟧ (conf config)
    ≡⟨⟩
      NCC.⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ (conf config)
    ≡⟨⟩
      NCC.⟦ translate (d ⟨ l , r ⟩) ⟧ (conf config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (conf config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves : ∀ {i : Size} {D A : Set}
    → (e : 2CC D i A)
    → NCC.⟦ translate e ⟧ ≅[ fnoc ][ conf ] 2CC.⟦ e ⟧
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

  2CC→NCC : ∀ {i : Size} {D : Set} → LanguageCompiler (2CCL D {i}) (NCCL (sucs zero) D {i})
  2CC→NCC .LanguageCompiler.compile = translate
  2CC→NCC .LanguageCompiler.config-compiler expr .to = conf
  2CC→NCC .LanguageCompiler.config-compiler expr .from = fnoc
  2CC→NCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)


-- A generalization which translates to an arbitrary n instead of 2.
2CC→NCC : ∀ {i : Size} {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (2CCL D {i}) (NCCL n D {i})
2CC→NCC n = 2Ary.2CC→NCC ⊕ NCC→NCC n

NCC≽2CC : ∀ {D : Set} → (n : ℕ≥ 2) → NCCL n D ≽ 2CCL D
NCC≽2CC n = expressiveness-from-compiler (2CC→NCC n)
