open import Framework.Construct using (_∈ₛ_)
open import Framework.Definitions using (𝔽; 𝕍)
open import Construct.Artifact as At using () renaming (Syntax to Artifact)

module Translation.Lang.Transitive.CCC-to-2CC (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Size using (Size)
open import Util.Nat.AtLeast using (sucs)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open CCC using (CCCL)
open 2CC using (2CCL)

open import Translation.Lang.CCC-to-NCC Variant Artifact∈ₛVariant using (CCC→NCC)
import Translation.Lang.NCC-to-2CC
open Translation.Lang.NCC-to-2CC.2Ary Variant Artifact∈ₛVariant using (NCC→2CC)


CCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (CCCL {i} D) (2CCL (D × ℕ))
CCC→2CC = CCC→NCC (sucs zero) ⊕ NCC→2CC

2CC≽CCC : ∀ {D : 𝔽} → 2CCL (D × ℕ) ≽ CCCL D
2CC≽CCC = expressiveness-from-compiler CCC→2CC
