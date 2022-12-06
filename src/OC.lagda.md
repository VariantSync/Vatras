# Option Calculus in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module OC where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Size using (Size; Size<_)
```

## Option Calculus

### Syntax

```agda
Option : Set
Option = String

data OC (i : Size) (A : Set) : Set where
  Artifact : ∀ {j : Size< i} →
    A → List (OC j A) → OC i A
  _❲_❳ : ∀ {j : Size< i} →
    Option → OC j A → OC i A
infixl 6 _❲_❳
```

### Semantics

```agda
open import SemanticDomains using (Variant; Artifactᵥ)
open import Data.Maybe using (Maybe; just; nothing)
open Data.List using (catMaybes; map)
open import Function using (flip)

{-| Configurations tell us which options to in- or exclude. True means include, false exclude. -}
Configuration : Set
Configuration = Option → Bool

-- These functions could also be implemented solely using lists but Maybe makes our intents more explicit
-- and thus more readable (in particular the use of catMaybes).

-- Semantics that may yield nothing in case a subtree was removed.
⟦_⟧' : ∀ {i : Size} {A : Set} → OC i A → Configuration → Maybe (Variant A)

-- recursive application of the semantics to all children of an artifact
⟦_⟧'-children : ∀ {i : Size} {A : Set} → List (OC i A) → Configuration → List (Variant A)
⟦ es ⟧'-children c =
  catMaybes -- keep everything that was chosen to be included and discard all nothing values occurring from removed options.
  (map (flip ⟦_⟧' c) es)

⟦ Artifact a es ⟧' c = just (Artifactᵥ a (⟦ es ⟧'-children c))
⟦ O ❲ e ❳ ⟧' c = if (c O)
                 then (⟦ e ⟧' c)
                 else nothing

-- Options at the root of an expression are mandatory.
-- We could also enforce this syntactically with a special root grammar rule that has to be
-- invoked first.
⟦_⟧ : ∀ {i : Size} {A : Set} → OC i A → Configuration → Variant A
⟦ Artifact a es ⟧ c = Artifactᵥ a (⟦ es ⟧'-children c)
⟦ O ❲ e ❳ ⟧ c       = ⟦ e ⟧ c
```

### Example and Test Time

Definitions:
```agda
open Size using (∞; ↑_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

OCExample : Set
OCExample = String × OC ∞ String
```

Some smart constructors:
```agda
leaf : ∀ {i : Size} {A : Set} → A → OC (↑ i) A
leaf a = Artifact a []

-- alternative name that does not require writing tortoise shell braces
opt : ∀ {i : Size} {A : Set} → Option → OC i A → OC (↑ i) A
opt O = _❲_❳ O
```

Show:
```agda
open Data.String using (_++_; intersperse)

showOC : ∀ {i : Size} → OC i String → String
showOC (Artifact s []) = s
showOC (Artifact s es@(_ ∷ _)) = s ++ "-<" ++ (intersperse ", " (map showOC es)) ++ ">-"
showOC (O ❲ e ❳) = O ++ "{" ++ showOC e ++ "}"
```

Examples:
```agda
optex-sandwich : OCExample
optex-sandwich = "sandwich" , Artifact "Buns" (
    "Tomato?" ❲ leaf "Tomato" ❳
  ∷ "Salad?"  ❲ leaf "Salad"  ❳
  ∷ "Cheese?" ❲ leaf "Cheese" ❳
  ∷ leaf "Mayonnaise" -- we always put mayo on the sandwich
  ∷ [])

optex-all : List OCExample
optex-all = (optex-sandwich ∷ [] )
```

```
open Data.String using (unlines)
open SemanticDomains using (showVariant)

optexp-1 : OCExample → String
optexp-1 (name , oc) = unlines (
    (name ++ " = " ++ showOC oc)
  ∷ ("[[" ++ name ++ "]] (λ x → true)  = " ++ showVariant (⟦ oc ⟧ (λ _ → true) ))
  ∷ ("[[" ++ name ++ "]] (λ x → false) = " ++ showVariant (⟦ oc ⟧ (λ _ → false)))
  ∷ [])
```

### Final Printing

```agda
mainStr : String
mainStr = intersperse "\n\n" (map optexp-1 optex-all)
```
