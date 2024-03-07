{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.FCC-to-BCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_) renaming (_,_ to _and_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (Size; ∞)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.BCC using (BCC; _-<_>-; _⟨_,_⟩) renaming (Configuration to BCCꟲ)
module BCC-Sem-1 D = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC-Sem-1 using (BCCL)
module BCC-Sem-2 {D} = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧₂)

import Lang.FCC
module FCC n = Lang.FCC n
open FCC using (FCC; _-<_>-; _⟨_⟩) renaming (Configuration to FCCꟲ)
module FCC-Sem-1 n D = Lang.FCC.Sem n D Variant Artifact∈ₛVariant
open FCC-Sem-1 using (FCCL)
module FCC-Sem-2 {n} {D} = Lang.FCC.Sem n D Variant Artifact∈ₛVariant
open FCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Translation.Lang.FCC-to-FCC Variant Artifact∈ₛVariant using (FCC→FCC)
open import Translation.Lang.FCC-to-FCC Variant Artifact∈ₛVariant using (IndexedDimension) public

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module 2Ary where
  translate : {i : Size} → {D A : Set} → FCC (sucs zero) D i A → BCC D ∞ A
  translate (a -< cs >-) = a -< List.map translate cs >-
  translate (d ⟨ l ∷ r ∷ [] ⟩) = d ⟨ translate l , translate r ⟩

  conf : {D : Set} → FCCꟲ (sucs zero) D → BCCꟲ D
  conf config d with config d
  ... | zero = true
  ... | suc zero = false

  fnoc : {D : Set} → BCCꟲ D → FCCꟲ (sucs zero) D
  fnoc config d with config d
  ... | true = zero
  ... | false = suc zero

  preserves-⊆ : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ translate expr ⟧₂ ⊆[ fnoc ] ⟦ expr ⟧ₙ
  preserves-⊆ (a -< cs >-) config =
    ⟦ translate (a -< cs >-) ⟧₂ config
    ≡⟨⟩
    ⟦ (a -< List.map translate cs >-) ⟧₂ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map translate cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧₂ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc config)) cs)
    ≡⟨⟩
    ⟦ a -< cs >- ⟧ₙ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l ∷ r ∷ [] ⟩) config =
    ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ config
    ≡⟨⟩
    ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ config
    ≡⟨⟩
    ⟦ if config d then translate l else translate r ⟧₂ config
    ≡⟨ Bool.push-function-into-if (λ e → ⟦ e ⟧₂ config) (config d) ⟩
    (if config d then ⟦ translate l ⟧₂ config else ⟦ translate r ⟧₂ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (config d)) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
    (if config d then ⟦ l ⟧ₙ (fnoc config) else ⟦ r ⟧ₙ (fnoc config))
    ≡⟨ lemma ⟩
    Vec.lookup (⟦ l ⟧ₙ (fnoc config) ∷ ⟦ r ⟧ₙ (fnoc config) ∷ []) (fnoc config d)
    ≡⟨ Vec.lookup-map (fnoc config d) (λ e → ⟦ e ⟧ₙ (fnoc config)) (l ∷ r ∷ []) ⟩
    ⟦ Vec.lookup (l ∷ r ∷ []) (fnoc config d) ⟧ₙ (fnoc config)
    ≡⟨⟩
    ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ (fnoc config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (fnoc config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves-⊇ : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ expr ⟧ₙ ⊆[ conf ] ⟦ translate expr ⟧₂
  preserves-⊇ (a -< cs >-) config =
    ⟦ a -< cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧₂ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ (conf config)) (List.map translate cs))
    ≡⟨⟩
    ⟦ (a -< List.map translate cs >-) ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ translate (a -< cs >-) ⟧₂ (conf config)
    ∎
  preserves-⊇ (d ⟨ l ∷ r ∷ [] ⟩) config =
    ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧ₙ config
    ≡˘⟨ Vec.lookup-map (config d) (λ e → ⟦ e ⟧ₙ config) (l ∷ r ∷ []) ⟩
    Vec.lookup (⟦ l ⟧ₙ config ∷ ⟦ r ⟧ₙ config ∷ []) (config d)
    ≡⟨ lemma ⟩
    (if conf config d then ⟦ l ⟧ₙ config else ⟦ r ⟧ₙ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (conf config d)) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
    (if conf config d then ⟦ translate l ⟧₂ (conf config) else ⟦ translate r ⟧₂ (conf config))
    ≡˘⟨ Bool.push-function-into-if (λ e → ⟦ e ⟧₂ (conf config)) (conf config d) ⟩
    ⟦ if conf config d then translate l else translate r ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ (conf config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if conf config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ translate expr ⟧₂ ≅[ fnoc ][ conf ] ⟦ expr ⟧ₙ
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

  FCC→BCC : {i : Size} → {D : Set} → LanguageCompiler (FCCL (sucs zero) D {i}) (BCCL D)
  FCC→BCC .LanguageCompiler.compile = translate
  FCC→BCC .LanguageCompiler.config-compiler expr .to = conf
  FCC→BCC .LanguageCompiler.config-compiler expr .from = fnoc
  FCC→BCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)


FCC→BCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (FCCL n D {i}) (BCCL (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
FCC→BCC n = FCC→FCC n (sucs zero) ⊕ 2Ary.FCC→BCC

BCC≽FCC : {D : Set} → (n : ℕ≥ 2) → BCCL (IndexedDimension D n) ≽ FCCL n D
BCC≽FCC n = expressiveness-from-compiler (FCC→BCC n)
