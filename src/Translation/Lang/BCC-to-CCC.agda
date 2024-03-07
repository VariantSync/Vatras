{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Translation.Lang.BCC-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (zero)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

import Lang.CCC
module CCC D = Lang.CCC.Sem D Variant Artifact∈ₛVariant
open CCC using (CCCL)

import Lang.BCC
module BCC D = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC using (BCCL)

import Translation.Lang.BCC-to-FCC
open Translation.Lang.BCC-to-FCC.2Ary Variant Artifact∈ₛVariant using (BCC→FCC)
open import Translation.Lang.FCC-to-CCC Variant Artifact∈ₛVariant using (FCC→CCC)


BCC→CCC : {i : Size} → {D : Set} → LanguageCompiler (BCCL D {i}) (CCCL D)
BCC→CCC = BCC→FCC ⊕ FCC→CCC (sucs zero)

CCC≽BCC : {D : Set} → CCCL D ≽ BCCL D
CCC≽BCC = expressiveness-from-compiler BCC→CCC
