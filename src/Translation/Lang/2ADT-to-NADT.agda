{-# OPTIONS --sized-types #-}

open import Framework.Definitions

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.2ADT-to-NADT (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (if_then_else_; true; false)
import Data.Bool.Properties as Bool
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using () renaming (_,_ to _and_)
open import Level using (0ℓ)
open import Size using (Size; ∞)

import Util.List as List
open import Framework.Relation.Function using (from; to)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

import Data.EqIndexedSet as IndexedSet
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Construct.Choices
open import Construct.GrulerArtifacts as GL using ()
open import Construct.NestedChoice using (value; choice)

open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts using (leaf)

import Lang.2ADT
module 2ADT where
  module 2ADT-Sem-1 F = Lang.2ADT F Variant
  open 2ADT-Sem-1 using (2ADT; 2ADTL; Configuration) public
  module 2ADT-Sem-2 {F} = Lang.2ADT F Variant
  open 2ADT-Sem-2 using (⟦_⟧) public
open 2ADT using (2ADT; 2ADTL)

import Lang.CCC
module CCC where
  open Lang.CCC public
  module CCC-Sem-1 F = Lang.CCC.Sem F Variant Artifact∈ₛVariant
  open CCC-Sem-1 using (CCCL) public
  module CCC-Sem-2 {F} = Lang.CCC.Sem F Variant Artifact∈ₛVariant
  open CCC-Sem-2 using (⟦_⟧) public
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)

import Lang.NADT
module NADT where
  open Lang.NADT Variant using (NADT; NADTAsset; NADTChoice) renaming (NADTVL to NADTL) public
  module NADT-Sem {F} = Lang.NADT Variant F
  open NADT-Sem using () renaming (semantics to ⟦_⟧) public -- TODO
open NADT using (NADT; NADTAsset; NADTChoice; NADTL)

import Translation.Construct.2Choice-to-Choice as 2Choice-to-Choice
open 2Choice-to-Choice.Translate using (convert)

artifact : ∀ {A : 𝔸} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


translate : ∀ {F : 𝔽} {A : 𝔸} → 2ADT F A → NADT F ∞ A
translate (2ADT.leaf a) = NADTAsset (leaf a)
translate {F = F} {A = A} (f 2ADT.⟨ l , r ⟩) = NADTChoice (f Choice.⟨ translate l ∷ translate r ∷ [] ⟩)

conf : ∀ {F : 𝔽} → 2ADT.Configuration F → CCC.Configuration F
conf config f with config f
... | true = 0
... | false = 1

fnoc : ∀ {F : 𝔽} → CCC.Configuration F → 2ADT.Configuration F
fnoc config f with config f
... | zero = true
... | suc _ = false

preserves-⊆ : ∀ {F : 𝔽} {A : 𝔸} → (expr : 2ADT F A) → NADT.⟦ translate expr ⟧ ⊆[ fnoc ] 2ADT.⟦ expr ⟧
preserves-⊆ (2ADT.leaf v) config = refl
preserves-⊆ (f 2ADT.⟨ l , r ⟩) config =
    NADT.⟦ NADTChoice (f Choice.⟨ translate l ∷ translate r ∷ [] ⟩) ⟧ config
  ≡⟨⟩
    NADT.⟦ List.find-or-last (config f) (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨ Eq.cong₂ NADT.⟦_⟧ lemma refl ⟩
    NADT.⟦ if fnoc config f then translate l else translate r ⟧ config
  ≡⟨ Bool.push-function-into-if (λ e → NADT.⟦ e ⟧ config) (fnoc config f) ⟩
    (if fnoc config f then NADT.⟦ translate l ⟧ config else NADT.⟦ translate r ⟧ config)
  ≡⟨ Eq.cong₂ (if fnoc config f then_else_) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
    (if fnoc config f then 2ADT.⟦ l ⟧ (fnoc config) else 2ADT.⟦ r ⟧ (fnoc config))
  ≡⟨⟩
    2ADT.⟦ f Lang.2ADT.⟨ l , r ⟩ ⟧ (fnoc config)
  ∎
  where
  lemma : List.find-or-last (config f) (translate l ∷ translate r ∷ []) ≡ (if fnoc config f then translate l else translate r)
  lemma with config f
  ... | zero = refl
  ... | suc _ = refl

preserves-⊇ : ∀ {F : 𝔽} {A : 𝔸} → (expr : 2ADT F A) → 2ADT.⟦ expr ⟧ ⊆[ conf ] NADT.⟦ translate expr ⟧
preserves-⊇ (2ADT.leaf v) config = refl
preserves-⊇ (f 2ADT.⟨ l , r ⟩) config =
    2ADT.⟦ f Lang.2ADT.⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    (if config f then 2ADT.⟦ l ⟧ config else 2ADT.⟦ r ⟧ config)
  ≡⟨ Eq.cong₂ (if config f then_else_) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
    (if config f then NADT.⟦ translate l ⟧ (conf config) else NADT.⟦ translate r ⟧ (conf config))
  ≡˘⟨ Bool.push-function-into-if (λ e → NADT.⟦ e ⟧ (conf config)) (config f) ⟩
    NADT.⟦ if config f then translate l else translate r ⟧ (conf config)
  ≡⟨ Eq.cong₂ NADT.⟦_⟧ lemma refl ⟩
    NADT.⟦ List.find-or-last (conf config f) (translate l ∷ translate r ∷ []) ⟧ (conf config)
  ≡⟨⟩
    NADT.⟦ NADTChoice (f Choice.⟨ translate l ∷ translate r ∷ [] ⟩) ⟧ (conf config)
  ∎
  where
  lemma : (if config f then translate l else translate r) ≡ List.find-or-last (conf config f) (translate l ∷ translate r ∷ [])
  lemma with config f
  ... | true = refl
  ... | false = refl

preserves : ∀ {F : 𝔽} {A : 𝔸} → (expr : 2ADT F A) → NADT.⟦ translate expr ⟧ ≅[ fnoc ][ conf ] 2ADT.⟦ expr ⟧
preserves expr = preserves-⊆ expr and preserves-⊇ expr

2ADT→NADT : ∀ {i : Size} {F : 𝔽} → LanguageCompiler (2ADTL F) (NADTL F)
2ADT→NADT .LanguageCompiler.compile = translate
2ADT→NADT .LanguageCompiler.config-compiler expr .to = conf
2ADT→NADT .LanguageCompiler.config-compiler expr .from = fnoc
2ADT→NADT .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

NADT≽2ADT : ∀ {F : 𝔽} → NADTL F ≽ 2ADTL F
NADT≽2ADT = expressiveness-from-compiler 2ADT→NADT
