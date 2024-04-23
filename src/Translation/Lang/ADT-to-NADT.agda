open import Framework.Definitions

module Translation.Lang.ADT-to-NADT where

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
open import Framework.Relation.Expressiveness using (expressiveness-from-compiler; _≽_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

import Data.EqIndexedSet as IndexedSet
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Construct.Choices
open import Construct.GrulerArtifacts as GL using ()
open import Construct.NestedChoice using (value; choice)

open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts using (leaf)

open import Lang.All
open ADT using (ADT; ADTL; _⟨_,_⟩)
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)
open NADT using (NADT; NADTL; NADTAsset; NADTChoice)

import Translation.Construct.2Choice-to-Choice as 2Choice-to-Choice
open 2Choice-to-Choice.Translate using (convert)

translate : ∀ {F : 𝔽} {A : 𝔸} → ADT F A → NADT F ∞ A
translate (ADT.leaf a) = NADTAsset (leaf a)
translate {F = F} {A = A} (f ADT.⟨ l , r ⟩) = NADTChoice (f Choice.⟨ translate l ∷ translate r ∷ [] ⟩)

conf : ∀ {F : 𝔽} → ADT.Configuration F → CCC.Configuration F
conf config f with config f
... | true = 0
... | false = 1

fnoc : ∀ {F : 𝔽} → CCC.Configuration F → ADT.Configuration F
fnoc config f with config f
... | zero = true
... | suc _ = false

preserves-⊆ : ∀ {F : 𝔽} {A : 𝔸} → (expr : ADT F A) → NADT.⟦ translate expr ⟧ ⊆[ fnoc ] ADT.⟦ expr ⟧
preserves-⊆ (ADT.leaf v) config = refl
preserves-⊆ (f ADT.⟨ l , r ⟩) config =
    NADT.⟦ NADTChoice (f Choice.⟨ translate l ∷ translate r ∷ [] ⟩) ⟧ config
  ≡⟨⟩
    NADT.⟦ List.find-or-last (config f) (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨ Eq.cong₂ NADT.⟦_⟧ lemma refl ⟩
    NADT.⟦ if fnoc config f then translate l else translate r ⟧ config
  ≡⟨ Bool.if-float (λ e → NADT.⟦ e ⟧ config) (fnoc config f) ⟩
    (if fnoc config f then NADT.⟦ translate l ⟧ config else NADT.⟦ translate r ⟧ config)
  ≡⟨ Eq.cong₂ (if fnoc config f then_else_) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
    (if fnoc config f then ADT.⟦ l ⟧ (fnoc config) else ADT.⟦ r ⟧ (fnoc config))
  ≡⟨⟩
    ADT.⟦ f ⟨ l , r ⟩ ⟧ (fnoc config)
  ∎
  where
  lemma : List.find-or-last (config f) (translate l ∷ translate r ∷ []) ≡ (if fnoc config f then translate l else translate r)
  lemma with config f
  ... | zero = refl
  ... | suc _ = refl

preserves-⊇ : ∀ {F : 𝔽} {A : 𝔸} → (expr : ADT F A) → ADT.⟦ expr ⟧ ⊆[ conf ] NADT.⟦ translate expr ⟧
preserves-⊇ (ADT.leaf v) config = refl
preserves-⊇ (f ⟨ l , r ⟩) config =
    ADT.⟦ f ⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    (if config f then ADT.⟦ l ⟧ config else ADT.⟦ r ⟧ config)
  ≡⟨ Eq.cong₂ (if config f then_else_) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
    (if config f then NADT.⟦ translate l ⟧ (conf config) else NADT.⟦ translate r ⟧ (conf config))
  ≡⟨ Bool.if-float (λ e → NADT.⟦ e ⟧ (conf config)) (config f) ⟨
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

preserves : ∀ {F : 𝔽} {A : 𝔸} → (expr : ADT F A) → NADT.⟦ translate expr ⟧ ≅[ fnoc ][ conf ] ADT.⟦ expr ⟧
preserves expr = preserves-⊆ expr and preserves-⊇ expr

ADT→NADT : ∀ {i : Size} {F : 𝔽} → LanguageCompiler (ADTL F) (NADTL F)
ADT→NADT .LanguageCompiler.compile = translate
ADT→NADT .LanguageCompiler.config-compiler expr .to = conf
ADT→NADT .LanguageCompiler.config-compiler expr .from = fnoc
ADT→NADT .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

NADT≽ADT : ∀ {F : 𝔽} → NADTL F ≽ ADTL F
NADT≽ADT = expressiveness-from-compiler ADT→NADT
