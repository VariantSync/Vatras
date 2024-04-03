# Overview of Language Relations

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.LanguageMap where
```

## Imports

```agda
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Size using (∞)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Variants using (Rose; Artifact∈ₛRose; Variant-is-VL)
Variant = Rose ∞
mkArtifact = Artifact∈ₛRose

open import Framework.Definitions using (𝕍; 𝔽)
open import Framework.Construct
open import Framework.Compiler
open import Framework.Relation.Expressiveness Variant using (_≽_; _⋡_; compiler-cannot-exist)
open import Framework.Proof.Transitive Variant using (less-expressive-from-completeness; completeness-by-expressiveness)
open import Framework.Properties.Completeness Variant using (Complete)
open import Util.Nat.AtLeast using (ℕ≥)

open import Construct.Artifact as At using () renaming (Syntax to Artifact)

open import Lang.All
open VariantList using (VariantListL; VariantList-is-Complete)
open CCC using (CCCL)
open NCC using (NCCL)
open 2CC using (2CCL)
open NADT using (NADTL)
open 2ADT using (2ADTL)
open OC using (WFOCL)

open CCC.Encode using () renaming (encoder to CCC-Rose-encoder)
```


## Core Choice Calculus vs Binary Choice Calculus

```agda
open import Translation.Lang.CCC-to-NCC Variant mkArtifact using (CCC→NCC; NCC≽CCC) public
open import Translation.Lang.NCC-to-CCC Variant mkArtifact using (NCC→CCC; CCC≽NCC) public

open import Translation.Lang.NCC.Grow Variant mkArtifact using (growCompiler) public
open import Translation.Lang.NCC.ShrinkTo2 Variant mkArtifact using (shrinkTo2Compiler) public
-- Generalization of the grow and shrink
open import Translation.Lang.NCC.NCC-to-NCC Variant mkArtifact using (NCC→NCC; NCC≽NCC) public

open import Translation.Lang.NCC-to-2CC Variant mkArtifact using (NCC→2CC; 2CC≽NCC) public
open import Translation.Lang.2CC-to-NCC Variant mkArtifact using (2CC→NCC; NCC≽2CC) public

open import Translation.Lang.Transitive.CCC-to-2CC Variant mkArtifact using (CCC→2CC; 2CC≽CCC) public
open import Translation.Lang.Transitive.2CC-to-CCC Variant mkArtifact using (2CC→CCC; CCC≽2CC) public
```

```agda
open import Translation.Lang.2CC-to-2ADT Variant mkArtifact using (2CC→2ADT; 2ADT≽2CC) public
-- open import Translation.Lang.2ADT-to-2CC Variant mkArtifact using () public

module _ {F : 𝔽} (_==_ : DecidableEquality F) where
  open import Translation.Lang.2ADT.DeadElim F Variant _==_ using (kill-dead-compiler) public

  open import Translation.Lang.2ADT-to-VariantList F Variant _==_ using (2ADT→VariantList; VariantList≽2ADT) public

import Translation.Lang.VariantList-to-CCC
module _ {F : 𝔽} (D : F) where
  open Translation.Lang.VariantList-to-CCC.Translate F D Variant mkArtifact CCC-Rose-encoder using (VariantList→CCC; CCC≽VariantList) public

open import Translation.Lang.2ADT-to-NADT Variant mkArtifact using (2ADT→NADT; NADT≽2ADT) public
open import Translation.Lang.NADT-to-CCC Variant mkArtifact using (NADT→CCC; CCC≽NADT) public
```

## Option Calculus vs Binary Choice Calculus
```agda
module _ {F : 𝔽} where
  open import Translation.Lang.OC-to-2CC F using (OC→2CC; 2CC≽OC) public
```

```agda
module _ {F : 𝔽} (D : F) where
  CCC-is-complete : Complete (CCCL F)
  CCC-is-complete = completeness-by-expressiveness VariantList-is-Complete (CCC≽VariantList D)

  NCC-is-complete : ∀ (n : ℕ≥ 2) → Complete (NCCL n (F × ℕ))
  NCC-is-complete n = completeness-by-expressiveness CCC-is-complete (NCC≽CCC n)

  2CC-is-complete : Complete (2CCL (F × ℕ))
  2CC-is-complete = completeness-by-expressiveness CCC-is-complete 2CC≽CCC

  2ADT-is-complete : Complete (2ADTL Variant (F × ℕ))
  2ADT-is-complete = completeness-by-expressiveness 2CC-is-complete 2ADT≽2CC

  NADT-is-complete : Complete (NADTL Variant (F × ℕ))
  NADT-is-complete = completeness-by-expressiveness 2ADT-is-complete NADT≽2ADT

  open OC.IncompleteOnRose using (OC-is-incomplete)

  OC-is-less-expressive-than-2CC : WFOCL F ⋡ 2CCL (F × ℕ)
  OC-is-less-expressive-than-2CC = less-expressive-from-completeness 2CC-is-complete OC-is-incomplete

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler (2CCL (F × ℕ)) (WFOCL F))
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-2CC
```
