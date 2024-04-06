{-# OPTIONS --sized-types #-}

module Test.Experiments.RoundTrip where

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

open import Framework.Compiler using (LanguageCompiler)
open import Framework.Definitions using (ℂ; 𝔸)
open import Framework.Variants using (Rose; Artifact∈ₛRose; show-rose)
open import Framework.VariabilityLanguage using (VariabilityLanguage; Expression)
open import Util.AuxProofs using (decidableEquality-×)
open import Util.Nat.AtLeast using (ℕ≥)
import Util.String as String

open import Lang.All
open import Translation.LanguageMap
import Translation.Lang.CCC-to-NCC
module CCC-to-NCC = Translation.Lang.CCC-to-NCC.Exact Variant mkArtifact
import Translation.Lang.NCC-to-2CC
open Translation.Lang.NCC-to-2CC.2Ary Variant mkArtifact using () renaming (NCC→2CC to NCC-2→2CC)

open import Show.Lines
open import Util.Named
open import Show.Eval

open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

Feature = String
Artifact : 𝔸
Artifact = String , String._≟_

open CCC-to-NCC using (⌈_⌉; numberOfAlternatives≤⌈_⌉)

CCC→NCC-Exact : (e : CCC.CCC Feature ∞ Artifact) → NCC.NCC ⌈ e ⌉ Feature ∞ Artifact
CCC→NCC-Exact e = CCC-to-NCC.translate ⌈ e ⌉ e (numberOfAlternatives≤⌈_⌉ e)


translate : {E₁ : Set} → {E₂ : E₁ → Set} → (e : E₁) → String → ((e : E₁) → E₂ e) → (E₂ e → Lines) → Lines' (E₂ e)
translate e E₂-name translator show = do
  linebreak
  [ Center ]> "│"
  [ Center ]> "          │ translate"
  [ Center ]> "↓"
  linebreak
  let e' = translator e
      pretty-e' = show e'
  [ Center ]> E₂-name
  overwrite-alignment-with Center
    (boxed (6 + width pretty-e') "" pretty-e')
  [ Center ]> "proven to have the same semantics as the previous expression"
  pure e'
  where
  open RawApplicative applicative

compile : ∀ {VL₁ VL₂ : VariabilityLanguage Variant}
  → Expression VL₁ Artifact
  → String
  → LanguageCompiler VL₁ VL₂
  → (Expression VL₂ Artifact → Lines)
  → Lines' (Expression VL₂ Artifact)
compile e VL₂-name compiler show = translate e VL₂-name (LanguageCompiler.compile compiler) show

round-trip : Experiment (OC.WFOC Feature ∞ (String , String._≟_))
getName round-trip = "Translate CCC in one round-trip into equally expressive variability languages"
get     round-trip ex@(name ≔ oc) = do
  [ Center ]> "OC, original expression"
  let pretty-oc = >_ (OC.Show.show-wfoc Feature id oc)
  overwrite-alignment-with Center
    (boxed (6 + width pretty-oc) "" pretty-oc)

  2cc         ← compile   oc          "2CC"         OC→2CC                              (2CC.Pretty.pretty id)
  2adt        ← compile   2cc         "2ADT"        2CC→2ADT                            (2ADT.pretty (show-rose id) id)
  variantList ← compile   2adt        "VariantList" (2ADT→VariantList String._≟_)       (VariantList.pretty (show-rose id))
  ccc         ← compile   variantList "CCC"         (VariantList→CCC "default feature") (CCC.pretty id)
  ncc         ← translate ccc         "NCC"         CCC→NCC-Exact                       (NCC.Pretty.pretty id)
  ncc2        ← compile   ncc         "NCC"         (shrinkTo2Compiler ⌈ ccc ⌉)         (NCC.Pretty.pretty (String.diagonal-ℕ ∘ map₂ Fin.toℕ))
  2cc'        ← compile   ncc2        "2CC"         NCC-2→2CC                           (2CC.Pretty.pretty (String.diagonal-ℕ ∘ map₂ Fin.toℕ))
  linebreak


open OC using (Root; _❲_❳; _-<_>-)

ex-sandwich : Example (OC.WFOC Feature ∞ Artifact)
ex-sandwich = "sandwich" ≔
  Root "bread"
    ( "salad?" ❲ "salad" -< [] >- ❳
    ∷ "cheese" -< [] >-
    ∷ "tofu?" ❲ "tofu" -< [] >- ❳
    ∷ "meat?" ❲ "meat" -< [] >- ❳
    ∷ "ketchup?" ❲ "ketchup" -< [] >- ❳
    ∷ "mayo?" ❲ "mayo" -< [] >- ❳
    ∷ []
    )

examples : List (Example (OC.WFOC Feature ∞ Artifact))
examples = ex-sandwich ∷ []
