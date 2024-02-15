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

open import Framework.Variants using (Rose; Artifact∈ₛRose)
Variant = Rose ∞
mkArtifact = Artifact∈ₛRose

open import Framework.Definitions using (𝕍; 𝔽)
open import Framework.Relation.Expressiveness Variant using (_⋡_)
open import Framework.Proof.Transitive Variant using (less-expressive-from-completeness)

import Lang.OC as OCL
import Lang.BCC as BCCL

-- DONE
import Translation.Lang.OC-to-BCC
-- import Translation.Lang.BCC-to-CCC

-- IN PROGRESS
-- import Translation.Lang.CCC-to-BCC
```

## Core Choice Calculus vs Binary Choice Calculus

```agda
-- open Translation.CCC-to-BCC using (
--   -- TODO: Still unproven
--   -- BCC-is-at-least-as-expressive-as-CCC
--   ) public

-- open Translation.BCC-to-CCC using (
--   CCC-is-at-least-as-expressive-as-BCC;
--   BCC→CCC-is-semantics-preserving
--   ) public
```

## Option Calculus vs Binary Choice Calculus

```agda
module _ (F : 𝔽) where
  open OCL.Sem  F Variant mkArtifact using (WFOCL)
  open BCCL.Sem F Variant mkArtifact using (BCCL)
  open OCL.IncompleteOnRose F using (OC-is-incomplete)

  {- TODO: Substitute completeness proof of BCC here. -}
  OC-is-less-expressive-than-BCC : WFOCL ⋡ BCCL
  OC-is-less-expressive-than-BCC = less-expressive-from-completeness {!!} OC-is-incomplete

open Translation.Lang.OC-to-BCC using (
  BCC-is-at-least-as-expressive-as-OC
  ) public
```
