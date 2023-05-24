# Option Calculus With Negations in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.NOC where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Size using (Size; ∞; ↑_)
open import Definitions
open import Lang.Annotation.Name using (Option)
```

## Syntax

```agda
data NOC : VarLang where
  Artifact : Artifactˡ NOC
  _❲_❳ : ∀ {i : Size} {A : Domain} →
    Option → NOC i A → NOC (↑ i) A
  ¬_❲_❳ : ∀ {i : Size} {A : Domain} →
    Option → NOC i A → NOC (↑ i) A
infixl 6 _❲_❳
infixl 6 ¬_❲_❳

data WFNOC : VarLang where
  Root : ∀ {i : Size} {A : Set} →
    A → List (NOC i A) → WFNOC (↑ i) A

forgetWF : ∀ {i : Size} {A : Domain} → WFNOC i A → NOC i A
forgetWF (Root a es) = Artifact a es
```

### Semantics

```agda
Configuration : Set
Configuration = Option → Bool

open import Data.Maybe using (Maybe; just; nothing)
open Data.List using (catMaybes; map)
open import Function using (flip)

-- ⟦_⟧ₒ : ∀ {i : Size} {A : Set} → NOC i A → Configuration → Maybe (Variant i A)
⟦_⟧ₒ : ∀ {i : Size} {A : Set} → NOC i A → Configuration → Maybe (Variant ∞ A)

-- recursive application of the semantics to all children of an artifact
-- ⟦_⟧ₒ-recurse : ∀ {i : Size} {A : Set} → List (NOC i A) → Configuration → List (Variant i A)
⟦_⟧ₒ-recurse : ∀ {i : Size} {A : Set} → List (NOC i A) → Configuration → List (Variant ∞ A)
⟦ es ⟧ₒ-recurse c =
  catMaybes -- Keep everything that was chosen to be included and discard all 'nothing' values occurring from removed options.
  (map (flip ⟦_⟧ₒ c) es)

⟦ Artifact a es ⟧ₒ c = just (Artifactᵥ a (⟦ es ⟧ₒ-recurse c))
⟦ O ❲ e ❳ ⟧ₒ c = if (c O)
                 then (⟦ e ⟧ₒ c)
                 else nothing
⟦ ¬ O ❲ e ❳ ⟧ₒ c = if (c O) -- define by recursing on the option with a manipulated config? No because that makes termination checking fial
                   then nothing
                   else (⟦ e ⟧ₒ c)
```

And now for the semantics of well-formed option calculus which just reuses the semantics of option calculus but we have the guarantee of the produced variants to exist.
```agda
-- ⟦_⟧ : ∀ {i : Size} {A : Domain} → WFNOC i A → Configuration → Variant i A
⟦_⟧ : Semantics WFNOC Configuration
⟦ Root a es ⟧ c = Artifactᵥ a (⟦ es ⟧ₒ-recurse c)

WFNOCL : VariabilityLanguage
WFNOCL = record
  { expression = WFNOC
  ; configuration = Configuration
  ; semantics = ⟦_⟧
  }
```

## Show

```agda
open Data.String using (_++_; intersperse)
open import Function using (_∘_)

show-noc : ∀ {i : Size} → NOC i String → String
show-noc (Artifact s []) = s
show-noc (Artifact s es@(_ ∷ _)) = s ++ "-<" ++ (intersperse ", " (map show-noc es)) ++ ">-"
show-noc (  O ❲ e ❳) =        O ++ "❲" ++ show-noc e ++ "❳"
show-noc (¬ O ❲ e ❳) = "¬" ++ O ++ "❲" ++ show-noc e ++ "❳"

show-wfnoc : ∀ {i : Size} → WFNOC i String → String
show-wfnoc = show-noc ∘ forgetWF
```

