# Option Calculus in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
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
open import Size using (Size; Size<_; ↑_)
open import Definitions using (Domain; VarLang; Variant; Artifactᵥ; Artifactˡ)
open import Lang.Annotation.Name using (Option)
```

## Syntax

```agda
data OC : VarLang where
  Artifact : Artifactˡ OC
  _❲_❳ : ∀ {i : Size} {j : Size< i} {A : Domain} →
    Option → OC j A → OC i A
infixl 6 _❲_❳
```

An expression is well-formed if there is an artifact at the root.
Otherwise, we would allow empty variants which would again require either (1) the assumption of the domain having an empty element or (2) the introduction of a symbole for the empty variant in the semantic domain (which most languages do not require).
This is issue is more deeply discussed in Paul's slides on option calculus.
```agda
data WFOC : VarLang where
  Root : ∀ {i : Size} {j : Size< i} {A : Set} →
    A → List (OC j A) → WFOC i A
```

Well-formedness can be forgotten, meaning that we lose the knowledge that an expression is well-formed in the type-system.
This knowledge is useful for simplifying function definitions where well-formedness does not matter, such as `show`.
```agda
forgetWF : ∀ {i : Size} {A : Domain} → WFOC i A → OC i A
forgetWF (Root a es) = Artifact a es

children-wf : ∀ {i : Size} {A : Domain} → WFOC (Size.↑_ i) A → List (OC i A)
children-wf (Root _ es) = es
```

### Semantics

Let's first define configurations. Configurations of option calculus tell us which options to in- or exclude. We define `true` to mean "include" and `false` to mean "exclude". Defining it the other way around would also be fine as long as we are consistent. Yet, our way of defining it is in line with if-semantics and how it is usually implemented in papers and tools.
```agda
Configuration : Set
Configuration = Option → Bool
```

The semantics recursively evaluates options given a configuration to cut-off all unselected trees and keep all selected trees.
Selected options will vanish from the expression because their variability was resolved.

First we define the semantics of pure option calculus, without any well-formedness constraints.
This may yield an empty variant which express using `Maybe`.
As `Maybe` is not in the semantic domain of our variability language, we cannot directly use our definitions for reasoning on variability languages.

Note: The following functions could also be implemented solely using lists but `Maybe` makes our intents more explicit and thus more readable (in particular the use of `catMaybes`).
```agda
open import Data.Maybe using (Maybe; just; nothing)
open Data.List using (catMaybes; map)
open import Function using (flip)

⟦_⟧ₒ : ∀ {i : Size} {A : Set} → OC i A → Configuration → Maybe (Variant A)

-- recursive application of the semantics to all children of an artifact
⟦_⟧ₒ-recurse : ∀ {i : Size} {A : Set} → List (OC i A) → Configuration → List (Variant A)
⟦ es ⟧ₒ-recurse c =
  catMaybes -- Keep everything that was chosen to be included and discard all 'nothing' values occurring from removed options.
  (map (flip ⟦_⟧ₒ c) es)

⟦ Artifact a es ⟧ₒ c = just (Artifactᵥ a (⟦ es ⟧ₒ-recurse c))
⟦ O ❲ e ❳ ⟧ₒ c = if (c O)
                 then (⟦ e ⟧ₒ c)
                 else nothing
```

And now for the semantics of well-formed option calculus which just reuses the semantics of option calculus but we have the guarantee of the produced variants to exist.
```agda
⟦_⟧ : ∀ {i : Size} {A : Set} → WFOC i A → Configuration → Variant A
⟦ Root a es ⟧ c = Artifactᵥ a (⟦ es ⟧ₒ-recurse c)
```

## Translations

Idea:

1. Prove completeness of core choice calculus as written on my note slides. Use n-ary choice calculus or ADDs for that to put all vairants into one big choice.
2. Prove incompleteness of option calculus. This is done below.
3. By (1) and transitivity of our translation we conclude that binary choice calculus is complete.
4. Prove that there can be no translation from binary choice calculus to option calculus because option calculus is incomplete. Assuming there would be a translation, we could translate a binary cc expression describing our counterexample from (2) which violates (2).

## Incompleteness

First, we need some imports.
```agda
open import Lang.Properties.Completeness using (Incomplete)
open import Data.Nat using (ℕ; suc)
open import Data.Product   using (_,_; ∃-syntax)
open import Util.Existence using (_,_)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

We prove incompleteness by showing that there exists at least one set of variants that cannot be described by option calculus.
In particular, any set of variants that includes two entirely distinct variants cannot be expressed because options cannot encode constraints such as alternatives in choice calculus.
As our counter example, we use the set `{0, 1}` as our variants:
```agda
variant-0 = Definitions.leaf 0
variant-1 = Definitions.leaf 1

variants-0-and-1 : List (Variant ℕ)
variants-0-and-1 = (variant-0 ∷ variant-1 ∷ [])
```
We stick to this concrete counter example instead of formulating the set of unrepresentable variants here to make the proof not more complicated than necessary.

We now prove that any well-formed option calculus expression `e` cannot be configured to `0` and `1` at the same time. The reason is that the expression `e` always has a domain element at the top. This element is always included in the variant and cannot simultaneously be `0` and `1`.
So we show that given an expression `e`, a proof that `e` can be configured to `0`, and a proof that `e` can be configured to `1`, we eventually conclude falsehood.
```agda
does-not-describe-variants-0-and-1 :
  ∀ {i : Size}
  → (e : WFOC i ℕ)
  → ∃[ c ] (⟦ e ⟧ c ≡ variant-0)
  → ∃[ c ] (⟦ e ⟧ c ≡ variant-1)
    ----------------------------
  → ⊥
-- If e has 0 as root, it may be configured to 0 but never to 1.
does-not-describe-variants-0-and-1 (Root 0       es) ∃c→⟦e⟧c≡0 ()
-- if e has a number larger than 1 at the top, it cannot be configured to yield 0.
does-not-describe-variants-0-and-1 (Root (suc n) es) ()
```

Finally, we can conclude incompleteness by showing that assuming completeness yields a contradiction using our definition above.
We pattern match on the assumed completeness evidence to unveil the expression `e` and the proofs that it can be configured to `0` and `1`.
```agda
OC-is-incomplete : Incomplete WFOC Configuration ⟦_⟧
OC-is-incomplete assumed-completeness with assumed-completeness variants-0-and-1
... | _ , e , (∃c→⟦e⟧c≡0 ∷ ∃c→⟦e⟧c≡1 ∷ []) , _ = does-not-describe-variants-0-and-1 e ∃c→⟦e⟧c≡0 ∃c→⟦e⟧c≡1
```

**This is an important result!**
It shows that we need at least some constraints to be complete.
This is a justification for choice calculus definiting variability annotations with constraints (being alternative) instead of being pure annotations.
Another way is to enrich the annotation language, for example using propositional logic.

## Utility

```agda
leaf : ∀ {i : Size} {A : Set} → A → OC (↑ i) A
leaf a = Artifact a []

-- alternative name that does not require writing tortoise shell braces
opt : ∀ {i : Size} {A : Set} → Option → OC i A → OC (↑ i) A
opt O = _❲_❳ O

open import Util.Named

all-oc : Bool → Configuration
all-oc b _ = b

allyes-oc : Named Configuration
allyes-oc = all-oc true called "all-yes"

allno-oc : Named Configuration
allno-oc = all-oc false called "all-no " --space intended for nicer printing lol
```

## Show

```agda
open Data.String using (_++_; intersperse)
open import Function using (_∘_)

show-oc : ∀ {i : Size} → OC i String → String
show-oc (Artifact s []) = s
show-oc (Artifact s es@(_ ∷ _)) = s ++ "-<" ++ (intersperse ", " (map show-oc es)) ++ ">-"
show-oc (O ❲ e ❳) = O ++ "❲" ++ show-oc e ++ "❳"

show-wfoc : ∀ {i : Size} → WFOC i String → String
show-wfoc = show-oc ∘ forgetWF
```

