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

open import Lang.NCC as NCC using (NCC; _-<_>-; _⟨_⟩)
module NCC-Sem-1 n D = NCC.Sem n D Variant Artifact∈ₛVariant
open NCC-Sem-1 using (NCCL)
module NCC-Sem-2 {n} {D} = NCC.Sem n D Variant Artifact∈ₛVariant
open NCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Lang.2CC as 2CC using (2CC; _-<_>-; _⟨_,_⟩)
module 2CC-Sem-1 D = 2CC.Sem D Variant Artifact∈ₛVariant
open 2CC-Sem-1 using (2CCL)
module 2CC-Sem-2 {D} = 2CC.Sem D Variant Artifact∈ₛVariant
open 2CC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧₂)

import Translation.Lang.NCC-to-NCC
open Translation.Lang.NCC-to-NCC.IncreaseArity Variant Artifact∈ₛVariant using (NCC→NCC)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module 2Ary where
  translate : {i : Size} → {D A : Set} → 2CC D i A → NCC (sucs zero) D i A
  translate (a -< cs >-) = a -< List.map translate cs >-
  translate (d ⟨ l , r ⟩) = d ⟨ translate l ∷ translate r ∷ [] ⟩

  conf : {D : Set} → 2CC.Configuration D → NCC.Configuration (sucs zero) D
  conf config d with config d
  ... | true = zero
  ... | false = suc zero

  fnoc : {D : Set} → NCC.Configuration (sucs zero) D → 2CC.Configuration D
  fnoc config d with config d
  ... | zero = true
  ... | suc zero = false

  preserves-⊆ : {i : Size} → {D A : Set} → (expr : 2CC D i A) → ⟦ translate expr ⟧ₙ ⊆[ fnoc ] ⟦ expr ⟧₂
  preserves-⊆ (a -< cs >-) config =
    ⟦ translate (a -< cs >-) ⟧ₙ config
    ≡⟨⟩
    ⟦ a -< List.map translate cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map translate cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ (fnoc config)) cs)
    ≡⟨⟩
    ⟦ a -< cs >- ⟧₂ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l , r ⟩) config =
    ⟦ translate (d ⟨ l , r ⟩) ⟧ₙ config
    ≡⟨⟩
    ⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup (translate l ∷ translate r ∷ []) (config d) ⟧ₙ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config d) translate (l ∷ r ∷ [])) refl ⟩
    ⟦ translate (Vec.lookup (l ∷ r ∷ []) (config d)) ⟧ₙ config
    ≡⟨ preserves-⊆ (Vec.lookup (l ∷ r ∷ []) (config d)) config ⟩
    ⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧₂ (fnoc config)
    ≡⟨ Eq.cong₂ ⟦_⟧₂ lemma refl ⟩
    ⟦ if (fnoc config d) then l else r ⟧₂ (fnoc config)
    ≡⟨⟩
    ⟦ d ⟨ l , r ⟩ ⟧₂ (fnoc config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if fnoc config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves-⊇ : {i : Size} → {D A : Set} → (expr : 2CC D i A) → ⟦ expr ⟧₂ ⊆[ conf ] ⟦ translate expr ⟧ₙ
  preserves-⊇ (a -< cs >-) config =
    ⟦ a -< cs >- ⟧₂ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧ₙ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (conf config)) (List.map translate cs))
    ≡⟨⟩
    ⟦ a -< List.map translate cs >- ⟧ₙ (conf config)
    ≡⟨⟩
    ⟦ translate (a -< cs >-) ⟧ₙ (conf config)
    ∎
  preserves-⊇ (d ⟨ l , r ⟩) config =
    ⟦ d ⟨ l , r ⟩ ⟧₂ config
    ≡⟨⟩
    ⟦ if config d then l else r ⟧₂ config
    ≡⟨⟩
    ⟦ if config d then l else r ⟧₂ config
    ≡⟨ preserves-⊇ (if config d then l else r) config ⟩
    ⟦ translate (if config d then l else r) ⟧ₙ (conf config)
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Bool.push-function-into-if (translate) (config d)) refl ⟩
    ⟦ if config d then translate l else translate r ⟧ₙ (conf config)
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ lemma refl ⟩
    ⟦ Vec.lookup (translate l ∷ translate r ∷ []) (conf config d) ⟧ₙ (conf config)
    ≡⟨⟩
    ⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ₙ (conf config)
    ≡⟨⟩
    ⟦ translate (d ⟨ l , r ⟩) ⟧ₙ (conf config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (conf config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves : {i : Size} → {D A : Set} → (e : 2CC D i A) → ⟦ translate e ⟧ₙ ≅[ fnoc ][ conf ] ⟦ e ⟧₂
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

  2CC→NCC : {i : Size} → {D : Set} → LanguageCompiler (2CCL D {i}) (NCCL (sucs zero) D {i})
  2CC→NCC .LanguageCompiler.compile = translate
  2CC→NCC .LanguageCompiler.config-compiler expr .to = conf
  2CC→NCC .LanguageCompiler.config-compiler expr .from = fnoc
  2CC→NCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)


2CC→NCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (2CCL D {i}) (NCCL n D {i})
2CC→NCC n = 2Ary.2CC→NCC ⊕ NCC→NCC n

NCC≽2CC : {D : Set} → (n : ℕ≥ 2) → NCCL n D ≽ 2CCL D
NCC≽2CC n = expressiveness-from-compiler (2CC→NCC n)
