# Option Calculus in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.OC where
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

An expression is well-formed if there is an artifact at the root.
```agda
data WellFormed : ∀ {i : Size} {A : Set} → OC i A → Set where
  Root : ∀ {i : Size} {A : Set}
    → (a : A)
    → (es : List (OC i A))
      --------------------------
    → WellFormed (Artifact a es)
```

### Semantics

Let's first define configurations. Configurations of option calculus tell us which options to in- or exclude. We define `true` to mean "include" and `false` to mean exclude. Defining it the other way around would also be fine as long as we are consistent. Yet, our way of defining it is in line with if-semantics and how it is usually implemented in papers and tools.
```agda
Configuration : Set
Configuration = Option → Bool
```

The semantics recursively evaluates options given a configuration to cut-off all unselected trees and keep all selected trees.
Selected options will vanish from the expression because their variability was resolved.

These following functions could also be implemented solely using lists but `Maybe` makes our intents more explicit and thus more readable (in particular the use of `catMaybes`).
```agda
open import SemanticDomains using (Variant; Artifactᵥ)
open import Data.Maybe using (Maybe; just; nothing)
open Data.List using (catMaybes; map)
open import Function using (flip)

-- Semantics that may yield nothing in case a subtree was removed.
⟦_⟧' : ∀ {i : Size} {A : Set} → OC i A → Configuration → Maybe (Variant A)

-- recursive application of the semantics to all children of an artifact
⟦_⟧'-children : ∀ {i : Size} {A : Set} → List (OC i A) → Configuration → List (Variant A)
⟦ es ⟧'-children c =
  catMaybes -- Keep everything that was chosen to be included and discard all 'nothing' values occurring from removed options.
  (map (flip ⟦_⟧' c) es)

⟦ Artifact a es ⟧' c = just (Artifactᵥ a (⟦ es ⟧'-children c))
⟦ O ❲ e ❳ ⟧' c = if (c O)
                 then (⟦ e ⟧' c)
                 else nothing

-- Old version of the semantics enforcing well-formedness implicitly in the semantics.
{-
-- Options at the root of an expression are mandatory.
-- We could also enforce this syntactically with a special root grammar rule that has to be
-- invoked first.
⟦_⟧ : ∀ {i : Size} {A : Set} → OC i A → Configuration → Variant A
⟦ Artifact a es ⟧ c = Artifactᵥ a (⟦ es ⟧'-children c)
⟦    O ❲ e ❳    ⟧ c = ⟦ e ⟧ c
-}

⟦_⟧ : ∀ {i : Size} {A : Set} {e : OC i A} → WellFormed e → Configuration → Variant A
⟦ Root a es ⟧ c = Artifactᵥ a (⟦ es ⟧'-children c)
```

### Translations

Idea:

1. Prove completeness of core choice calculus as written on my note slides. Use n-ary choice calculus or ADDs for that to put all vairants into one big choice.
2. Prove incompleteness of option calculus by showing that there exists at least one set of variants that cannot be described. The simplest counterexample here should be a set of two different symbols `{ leaf "a" , leaf "b" }`.
3. By (1) and transitivity of our translation we conclude that binary choice calculus is complete.
4. Prove that there can be no translation from binary choice calculus to option calculus because option calculus is incomplete. Assuming there would be a translation, we could translate a binary cc expression describing our counterexample from (2) which violates (2).

### Example and Test Time

Definitions:
```agda
open Size using (∞; ↑_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

record OCExample : Set where
  constructor example_is_which-is-wellformed-because_
  field
    name : String
    expr : OC ∞ String
    wf   : WellFormed expr

makeEx : {e : OC ∞ String} → String → WellFormed e → OCExample
makeEx {e} name wf = example name is e which-is-wellformed-because wf
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
optex-sandwich = makeEx "sandwich" (Root "Buns" (
    "Tomato?" ❲ leaf "Tomato" ❳
  ∷ "Salad?"  ❲ leaf "Salad"  ❳
  ∷ "Cheese?" ❲ leaf "Cheese" ❳
  ∷ leaf "Mayonnaise" -- we always put mayo on the sandwich
  ∷ []))

optex-all : List OCExample
optex-all = (optex-sandwich ∷ [] )
```

```
open Data.String using (unlines)
open SemanticDomains using (showVariant)

optexp-1 : OCExample → String
optexp-1 (example name is oc which-is-wellformed-because wf) = unlines (
    (name ++ " = " ++ showOC oc)
  ∷ ("[[" ++ name ++ "]] (λ x → true)  = " ++ showVariant (⟦ wf ⟧ (λ _ → true) ))
  ∷ ("[[" ++ name ++ "]] (λ x → false) = " ++ showVariant (⟦ wf ⟧ (λ _ → false)))
  ∷ [])
```

### Final Printing

```agda
mainStr : String
mainStr = intersperse "\n\n" (map optexp-1 optex-all)
```
