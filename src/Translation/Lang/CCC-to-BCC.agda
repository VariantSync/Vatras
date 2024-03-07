{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact as At using () renaming (Syntax to Artifact)

module Translation.Lang.CCC-to-BCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

import Lang.CCC
module CCC-Sem D = Lang.CCC.Sem D Variant Artifact∈ₛVariant
open CCC-Sem using (CCCL)

import Lang.BCC
module BCC-Sem D = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC-Sem using (BCCL)

open import Translation.Lang.CCC-to-FCC Variant Artifact∈ₛVariant using (CCC→FCC)
import Translation.Lang.FCC-to-BCC
open Translation.Lang.FCC-to-BCC.2Ary Variant Artifact∈ₛVariant using (FCC→BCC)


CCC→BCC : {i : Size} → {D : Set} → LanguageCompiler (CCCL D {i}) (BCCL (D × ℕ))
CCC→BCC = CCC→FCC (sucs zero) ⊕ FCC→BCC

BCC≽CCC : {D : Set} → BCCL (D × ℕ) ≽ CCCL D
BCC≽CCC = expressiveness-from-compiler CCC→BCC
