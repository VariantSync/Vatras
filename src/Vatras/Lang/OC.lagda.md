# Option Calculus in Agda

This module formalizes option calculus, a new language for variability
we introduce to capture variability with exactly and only optional variability.

## Module

```agda
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; 𝔼; ℂ)
module Vatras.Lang.OC (Option : 𝔽) where
```

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Size using (Size; ∞; ↑_)
open import Function using (_∘_)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage
```

## Syntax

An option calculus expression is either an artifact `a -< es >-` (just as in [rose trees](../Framework/Variants.agda))
or an option `O ❲ e ❳` which optionally includes a sub-expression `e` in case `O` gets selected.
```agda
data OC : Size → 𝔼 where
  _-<_>- : ∀ {i A} → atoms A → List (OC i A) → OC (↑ i) A
  _❲_❳ : ∀ {i : Size} {A : 𝔸} → Option → OC i A → OC (↑ i) A
infixl 6 _❲_❳

{-|
Creates a leaf artifact node.
-}
oc-leaf : ∀ {i : Size} {A : 𝔸} → atoms A → OC (↑ i) A
oc-leaf a = a -< [] >-

{-|
This is an alternative constructor for options to avoid typing tortoise shell braces.
-}
opt : ∀ {i : Size} {A : 𝔸}  → Option → OC i A → OC (↑ i) A
opt = _❲_❳
```

An expression is well-formed if there is an artifact at the root.
Otherwise, we would allow empty variants which would again require either (1) the assumption of the domain having an empty element or (2) the introduction of a symbol for the empty variant in the semantic domain (which most languages do not require).
We discuss this problem in detail in our paper.

To ensure well-formedness, we introduce the following auxiliary type which forces there to be an artifact at the root:
```agda
data WFOC : Size → 𝔼 where
  Root : ∀ {i A} → atoms A → List (OC i A) → WFOC (↑ i) A
```

Well-formedness can be forgotten, meaning that we lose the knowledge that an expression is well-formed in the type-system.
This knowledge is useful for simplifying function definitions where well-formedness does not matter, such as `show`.
```agda
forgetWF : ∀ {i : Size} {A : 𝔸} → WFOC i A → OC i A
forgetWF (Root a es) = a -< es >-

children-wf : ∀ {i : Size} {A : 𝔸} → WFOC (Size.↑_ i) A → List (OC i A)
children-wf (Root _ es) = es
```

### Semantics

Let's first define configurations.
Configurations of option calculus tell us which options to include or exclude.
We define `true` to mean "include" and `false` to mean "exclude".
Defining it the other way around would also be fine as long as we are consistent.
Yet, our way of defining it is in line with if-semantics and how it is usually implemented in papers and tools.
```agda
Configuration : ℂ
Configuration = Option → Bool
```

The semantics recursively evaluates options given a configuration to cut-off all unselected trees and keep all selected trees.
Selected options will vanish from the expression because their variability was resolved.

First we define the semantics of pure option calculus, without any well-formedness constraints.
This may yield an empty variant which we express using `Maybe`.
As `Maybe` is not in the semantic domain of our variability language, we cannot directly use our definitions for reasoning on variability languages.

Note: The following functions could also be implemented solely using lists but `Maybe` makes our intents more explicit and thus more readable (in particular the use of `catMaybes`).
```agda
open import Data.Maybe using (Maybe; just; nothing)
open Data.List using (catMaybes; map)
open import Function using (flip)

{-|
Conventional Semantics of Option Calculus that dismisses all empty values
except of there is an empty value at the top.
-}
mutual
  {-|
  Recursive application of the semantics to all children of an artifact.
  -}
  -- ⟦_⟧ₒ-recurse : ∀ {i A} → List (OC i A) → Configuration → List (V A)
  ⟦_⟧ₒ-recurse : ∀ {i} → 𝔼-Semantics (List ∘ Rose ∞) Configuration (List ∘ OC i)
  ⟦ es ⟧ₒ-recurse c =
    catMaybes -- Keep everything that was chosen to be included and discard all 'nothing' values occurring from removed options.
    (map (flip ⟦_⟧ₒ c) es)

  {-|
  Semantics of non-well-formed option calculus.
  -}
  ⟦_⟧ₒ : ∀ {i : Size} → 𝔼-Semantics (Maybe ∘ Rose ∞) Configuration (OC i)
  ⟦ a -< es >- ⟧ₒ c = just (a V.-< ⟦ es ⟧ₒ-recurse c >-)
  ⟦ O ❲ e ❳ ⟧ₒ c = if c O then ⟦ e ⟧ₒ c else nothing

{-|
Interestingly, option calculus without an artifact root still forms a variability language
but only if the adapt the type of variants to also allow the empty variant, encoded via Maybe.
-}
OCL : ∀ {i : Size} → VariabilityLanguage (Maybe ∘ Rose ∞)
OCL {i} = ⟪ OC i , Configuration , ⟦_⟧ₒ ⟫
```

And now for the semantics of well-formed option calculus which just reuses the semantics of option calculus but we have the guarantee of the produced variants to exist.
```agda
⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics (Rose ∞) Configuration (WFOC i)
⟦ Root a es ⟧ c = a V.-< ⟦ es ⟧ₒ-recurse c >-

WFOCL : ∀ {i : Size} → VariabilityLanguage (Rose ∞)
WFOCL {i} = ⟪ WFOC i , Configuration , ⟦_⟧ ⟫
```
