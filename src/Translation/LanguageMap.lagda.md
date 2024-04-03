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
open import Size using (∞)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Variants using (Rose; Artifact∈ₛRose; Variant-is-VL)
Variant = Rose ∞
mkArtifact = Artifact∈ₛRose

open import Framework.Definitions using (𝕍; 𝔽)
open import Framework.Construct
open import Framework.Compiler
open import Framework.Relation.Expressiveness Variant using (_⋡_; compiler-cannot-exist)
open import Framework.Proof.Transitive Variant using (less-expressive-from-completeness)

open import Construct.Artifact as At using () renaming (Syntax to Artifact)

open import Lang.All
open OC using (WFOCL)
open 2CC using (2CCL)

-- DONE
import Translation.Lang.OC-to-2CC
-- import Translation.Lang.2CC-to-CCC

-- IN PROGRESS
-- import Translation.Lang.CCC-to-2CC
```

## Core Choice Calculus vs Binary Choice Calculus

```agda
-- open Translation.CCC-to-2CC using (
--   -- TODO: Still unproven
--   -- 2CC-is-at-least-as-expressive-as-CCC
--   ) public

-- open Translation.2CC-to-CCC using (
--   CCC-is-at-least-as-expressive-as-2CC;
--   2CC→CCC-is-semantics-preserving
--   ) public

-- For any type of variant that we can encode in CCC:
-- - CCC is complete
-- - CCC ≽ VariantList
-- We only assume the existence of an annotation language F, which
-- contains at least one expression D : F, no matter how it looks.
module CCC-Props (F : 𝔽) (D : F) where
  open CCC.Encode using (encoder)

  import Translation.Lang.VariantList-to-CCC F D Variant mkArtifact as VL→CCC
  open VL→CCC.Translate encoder using (
    CCCL-is-at-least-as-expressive-as-VariantListL;
    CCCL-is-complete
    ) public
```

## Option Calculus vs Binary Choice Calculus

```agda
module _ (F : 𝔽) where
  open OC.IncompleteOnRose using (OC-is-incomplete)

  {- TODO: Substitute completeness proof of 2CC here. -}
  OC-is-less-expressive-than-2CC : WFOCL F ⋡ 2CCL F
  OC-is-less-expressive-than-2CC = less-expressive-from-completeness {!!} OC-is-incomplete

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler (2CCL F) (WFOCL F))
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-2CC

open Translation.Lang.OC-to-2CC using (
  2CC≽OC
  ) public
```
