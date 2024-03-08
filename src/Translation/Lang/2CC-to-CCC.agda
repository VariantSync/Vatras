{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Translation.Lang.2CC-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (zero)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

import Lang.CCC
module CCC D = Lang.CCC.Sem D Variant Artifact∈ₛVariant
open CCC using (CCCL)

import Lang.2CC
module 2CC D = Lang.2CC.Sem D Variant Artifact∈ₛVariant
open 2CC using (2CCL)

import Translation.Lang.2CC-to-NCC
open Translation.Lang.2CC-to-NCC.2Ary Variant Artifact∈ₛVariant using (2CC→NCC)
open import Translation.Lang.NCC-to-CCC Variant Artifact∈ₛVariant using (NCC→CCC)


2CC→CCC : {i : Size} → {D : Set} → LanguageCompiler (2CCL D {i}) (CCCL D)
2CC→CCC = 2CC→NCC ⊕ NCC→CCC (sucs zero)

CCC≽2CC : {D : Set} → CCCL D ≽ 2CCL D
CCC≽2CC = expressiveness-from-compiler 2CC→CCC
