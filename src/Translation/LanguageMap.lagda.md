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

### Languages

```agda
open import Lang.OC
     using (OC; WFOC; WFOCL; ⟦_⟧; ⟦_⟧ₒ; OC-is-incomplete)
  renaming (Configuration to Confₒ)
open import Lang.BCC
     using (BCC; BCCL)
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Configuration to Conf₂
           )
```

### Properties and Relations

```agda
open import Lang.Properties.Completeness
open import Relations.Semantic
```

### Translations
```agda
-- DONE
import Translation.OC-to-BCC
import Translation.BCC-to-CCC

-- IN PROGRESS
import Translation.CCC-to-BCC

-- TODO
import Translation.ADD-to-BCC
import Translation.BCC-to-ADD

-- import Translation.VT-to-BCC
-- import Translation.BCC-to-VT
-- import Translation.VT-to-OC -- impossible
-- import Translation.OC-to-VT
```

## Core Choice Calculus vs Binary Choice Calculus

```agda
open Translation.CCC-to-BCC using (
  -- TODO: Still unproven
  -- BCC-is-at-least-as-expressive-as-CCC
  ) public

open Translation.BCC-to-CCC using (
  CCC-is-at-least-as-expressive-as-BCC;
  BCC→CCC-is-semantics-preserving
  ) public
```

## Option Calculus vs Binary Choice Calculus

```agda
{- TODO: Substitute completeness proof of BCC here. -}
OC-is-less-expressive-than-BCC : WFOCL is-less-expressive-than BCCL
OC-is-less-expressive-than-BCC = less-expressive-from-completeness {!!} OC-is-incomplete

open Translation.OC-to-BCC using (
  BCC-is-at-least-as-expressive-as-OC;
  OC→BCC-is-semantics-preserving
  ) public
```

## Algebraic Decision Diagrams vs Binary Choice Calculus

```agda
open Translation.BCC-to-ADD using (
  -- ADD-is-at-least-as-expressive-as-BCC
  ) public

open Translation.ADD-to-BCC using (
  -- BCC-is-at-least-as-expressive-as-ADD
  -- ADD→BCC-is-semantics-preserving
  ) public
```

## Variation Trees vs Binary Choice Calculus

```agda
-- TODO
```

## Variation Trees vs Option Calculus

```agda
-- TODO
```

