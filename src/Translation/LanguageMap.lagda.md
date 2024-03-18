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

import Lang.OC
import Lang.2CC
import Lang.CCC

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
  open Lang.CCC.Sem F Variant mkArtifact
  open Lang.CCC.Encode F using (encoder)

  import Translation.Lang.VariantList-to-CCC F D Variant mkArtifact as VL→CCC
  open VL→CCC.Translate encoder using (
    CCCL-is-at-least-as-expressive-as-VariantListL;
    CCCL-is-complete
    ) public
```

## Option Calculus vs Binary Choice Calculus

```agda
module _ (F : 𝔽) where
  open Lang.OC.Sem  F Variant mkArtifact using (WFOCL)
  open Lang.2CC.Sem F Variant mkArtifact using (2CCL)
  open Lang.OC.IncompleteOnRose F using (OC-is-incomplete)

  {- TODO: Substitute completeness proof of 2CC here. -}
  OC-is-less-expressive-than-2CC : WFOCL ⋡ 2CCL
  OC-is-less-expressive-than-2CC = less-expressive-from-completeness {!!} OC-is-incomplete

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler 2CCL WFOCL)
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-2CC

open Translation.Lang.OC-to-2CC using (
  2CC≽OC
  ) public
```
