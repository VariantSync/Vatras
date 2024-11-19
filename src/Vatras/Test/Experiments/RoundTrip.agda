module Vatras.Test.Experiments.RoundTrip where

open import Data.Bool using (Bool; true; false)
import Data.Fin as Fin
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat using (_+_)
open import Data.Product using (_,_; proj₁; proj₂; map₂)
open import Data.String as String using (String; _++_; unlines; _==_)
open import Effect.Applicative using (RawApplicative)

open import Size using (Size; ∞)
open import Function using (id; _∘_)
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (ℂ; 𝔸)
open import Vatras.Framework.Variants using (Rose; show-rose)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; Expression)
open import Vatras.Util.AuxProofs using (decidableEquality-×)
open import Vatras.Util.Nat.AtLeast using (ℕ≥)
import Vatras.Util.String as String

open import Vatras.Lang.All
open CCC using (CCC; _⟨_⟩; _-<_>-)
open NCC using (NCC)
open import Vatras.Translation.LanguageMap
import Vatras.Translation.Lang.CCC-to-NCC
module CCC-to-NCC = Vatras.Translation.Lang.CCC-to-NCC.Exact
import Vatras.Translation.Lang.NCC-to-2CC
open Vatras.Translation.Lang.NCC-to-2CC.2Ary using () renaming (NCC→2CC to NCC-2→2CC)
open CCC.Encode using () renaming (encoder to CCC-Rose-encoder)

open import Vatras.Show.Lines
open import Vatras.Util.Named
open import Vatras.Show.Eval

open import Vatras.Test.Experiment
open import Vatras.Test.Example
open import Vatras.Test.Examples.OC

Feature = String
Artifact : 𝔸
Artifact = String , String._≟_

open CCC-to-NCC using (⌈_⌉; numberOfAlternatives≤⌈_⌉)

CCC→NCC-Exact : (e : CCC Feature ∞ Artifact) → NCC Feature ⌈ e ⌉ ∞ Artifact
CCC→NCC-Exact e = CCC-to-NCC.translate ⌈ e ⌉ e (numberOfAlternatives≤⌈_⌉ e)


translate : {E₁ : Set₁} → {E₂ : E₁ → Set₁} → (e : E₁) → String → ((e : E₁) → E₂ e) → (E₂ e → Lines) → Lines' (E₂ e)
translate e E₂-name translator show = return-level e' do
  linebreak
  [ Center ]> "│"
  [ Center ]> "          │ translate"
  [ Center ]> "↓"
  linebreak
  [ Center ]> E₂-name
  overwrite-alignment-with Center
    (boxed (6 + width pretty-e') "" pretty-e')
  [ Center ]> "proven to have the same semantics as the previous expression"
  where
  e' = translator e
  pretty-e' = show e'

compile : ∀ {VL₁ VL₂ : VariabilityLanguage Variant}
  → Expression VL₁ Artifact
  → String
  → LanguageCompiler VL₁ VL₂
  → (Expression VL₂ Artifact → Lines)
  → Lines' (Expression VL₂ Artifact)
compile e VL₂-name compiler show = translate e VL₂-name (LanguageCompiler.compile compiler) show

round-trip : Experiment (CCC Feature ∞ (String , String._≟_))
getName round-trip = "Translate CCC in one round-trip into equally expressive variability languages"
get     round-trip ex@(name ≔ ccc) = do
  [ Center ]> "CCC, original expression"
  let pretty-ccc = CCC.pretty id ccc
  overwrite-alignment-with Center
    (boxed (6 + width pretty-ccc) "" pretty-ccc)

  void-level do
    ncc         ← translate ccc         "NCC"         CCC→NCC-Exact                                              (NCC.Pretty.pretty id)
    ncc2        ← compile   ncc         "NCC"         (shrinkTo2Compiler ⌈ ccc ⌉)                                (NCC.Pretty.pretty (String.diagonal-ℕ ∘ map₂ Fin.toℕ))
    2cc         ← compile   ncc2        "2CC"         NCC-2→2CC                                                  (2CC.Pretty.pretty (String.diagonal-ℕ ∘ map₂ Fin.toℕ))
    adt         ← compile   2cc         "ADT"         2CC→ADT                                                    (ADT.pretty (show-rose id) (String.diagonal-ℕ ∘ map₂ Fin.toℕ))
    variantList ← compile   adt         "VariantList" (ADT→VariantList (decidableEquality-× String._≟_ Fin._≟_)) (VariantList.pretty (Rose ∞) (show-rose id))
    do            compile   variantList "CCC"         (VariantList→CCC "default feature" CCC-Rose-encoder)       (CCC.pretty id)
  linebreak


ex-trivial : Example (CCC Feature ∞ Artifact)
ex-trivial = "trivial" ≔ "D" ⟨ "l" -< [] >- ∷ "r" -< [] >- ∷ [] ⟩

ex-sandwich : Example (CCC Feature ∞ Artifact)
ex-sandwich = "Sandwich Recipe" ≔
  "🍞"
    -< "Salad?"
         ⟨ "🥗" -< [] >-
         ∷ "ε" -< [] >-
         ∷ []
         ⟩
    ∷  "🧀" -< [] >-
    ∷  "Patty?"
         ⟨ "🍖" -< [] >-
         ∷ "🧆" -< [] >-
         ∷ []
         ⟩
    ∷  "Sauce?"
         ⟨ "ε" -< [] >-
         ∷ "🥚" -< [] >-
         ∷ "🍅" -< [] >-
         ∷ "🍅🥚" -< [] >-
         ∷ []
         ⟩
    ∷ []
    >-

examples : List (Example (CCC Feature ∞ Artifact))
examples = ex-trivial ∷ ex-sandwich ∷ []
