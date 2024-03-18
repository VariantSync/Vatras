{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact as At using () renaming (Syntax to Artifact)

module Translation.Lang.Transitive.CCC-to-2CC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔽)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

import Lang.CCC
module CCC-Sem D = Lang.CCC.Sem D Variant Artifact∈ₛVariant
open CCC-Sem using (CCCL)

import Lang.2CC
module 2CC-Sem D = Lang.2CC.Sem D Variant Artifact∈ₛVariant
open 2CC-Sem using (2CCL)

open import Translation.Lang.CCC-to-NCC Variant Artifact∈ₛVariant using (CCC→NCC)
import Translation.Lang.NCC-to-2CC
open Translation.Lang.NCC-to-2CC.2Ary Variant Artifact∈ₛVariant using (NCC→2CC)


CCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (CCCL D {i}) (2CCL (D × ℕ))
CCC→2CC = CCC→NCC (sucs zero) ⊕ NCC→2CC

2CC≽CCC : ∀ {D : 𝔽} → 2CCL (D × ℕ) ≽ CCCL D
2CC≽CCC = expressiveness-from-compiler CCC→2CC
