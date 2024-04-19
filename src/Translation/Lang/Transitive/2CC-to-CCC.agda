open import Framework.Construct using (_∈ₛ_)
open import Framework.Definitions using (𝔽; 𝕍)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Translation.Lang.Transitive.2CC-to-CCC (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (zero)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open CCC using (CCCL)
open 2CC using (2CCL)

import Translation.Lang.2CC-to-NCC
open Translation.Lang.2CC-to-NCC.2Ary Variant Artifact∈ₛVariant using (2CC→NCC)
open import Translation.Lang.NCC-to-CCC Variant Artifact∈ₛVariant using (NCC→CCC)


2CC→CCC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (2CCL {i} D) (CCCL D)
2CC→CCC = 2CC→NCC ⊕ NCC→CCC (sucs zero)

CCC≽2CC : ∀ {D : 𝔽} → CCCL D ≽ 2CCL D
CCC≽2CC = expressiveness-from-compiler 2CC→CCC
