# Option Calculus in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Framework.Definitions
module Lang.OC where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.String as String using (String)
open import Size using (Size; ∞; ↑_)
open import Function using (_∘_)

open import Framework.Variants
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
```

## Syntax

```agda
data OC (Option : 𝔽) : Size → 𝔼 where
  {-|
  FIXME:
  We do not reuse the artifact constructor here.
  Below is a commented out variant of this type where we
  reuse that constructor.
  However, for some unfathomable reason then termination
  checking fails within OC-to-2CC.agda
  because prepending an 'OC i A' to a 'Vec (OC (↑ i) A) n'
  is illegal then (but as of now just works).
  I have no idea what's the reason for this.
  Maybe reusing Artifact hides something from the Agda
  compiler that it needs for termination checking.
  -}
  _-<_>- : ∀ {i A} → atoms A → List (OC Option i A) → OC Option (↑ i) A
  _❲_❳ : ∀ {i : Size} {A : 𝔸} →
    Option → OC Option i A → OC Option (↑ i) A
infixl 6 _❲_❳

-- data OC : Size → 𝔼 where
--   atom : ∀ {i A} → Artifact (OC i) A → OC (↑ i) A
--   _❲_❳ : ∀ {i : Size} {A : 𝔸} →
--     Option → OC i A → OC (↑ i) A
-- infixl 6 _❲_❳
-- pattern _-<_>- a cs  = atom (a At.-< cs >-)
```

An expression is well-formed if there is an artifact at the root.
Otherwise, we would allow empty variants which would again require either (1) the assumption of the domain having an empty element or (2) the introduction of a symbol for the empty variant in the semantic domain (which most languages do not require).
```agda
data WFOC (Option : 𝔽) : Size → 𝔼 where
  WRoot : ∀ {i A} → Artifact (OC Option i) A → WFOC Option (↑ i) A
pattern Root a cs  = WRoot (a At.-< cs >-)
```

Well-formedness can be forgotten, meaning that we lose the knowledge that an expression is well-formed in the type-system.
This knowledge is useful for simplifying function definitions where well-formedness does not matter, such as `show`.
```agda
forgetWF : ∀ {i : Size} {Option : 𝔽} {A : 𝔸} → WFOC Option i A → OC Option i A
forgetWF (Root a es) = a -< es >-

children-wf : ∀ {i : Size} {Option : 𝔽} {A : 𝔸} → WFOC Option (Size.↑_ i) A → List (OC Option i A)
children-wf (Root _ es) = es
```

### Semantics

Let's first define configurations. Configurations of option calculus tell us which options to in- or exclude. We define `true` to mean "include" and `false` to mean "exclude". Defining it the other way around would also be fine as long as we are consistent. Yet, our way of defining it is in line with if-semantics and how it is usually implemented in papers and tools.
```agda
Configuration : 𝔽 → 𝕂
Configuration Option = Option → Bool
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

{-|
Conventional Semantics of Option Calculus that dismisses all empty values
except of there is an empty value at the top.
-}
module Sem (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where mutual
  OCL : ∀ {i : Size} (Option : 𝔽) → VariabilityLanguage (Maybe ∘ V)
  OCL {i} Option = ⟪ OC Option i , Configuration Option , ⟦_⟧ₒ ⟫

  ⟦_⟧ₒ : ∀ {i : Size} {Option : 𝔽} → 𝔼-Semantics (Maybe ∘ V) (Configuration Option) (OC Option i)

  -- -- recursive application of the semantics to all children of an artifact
  -- ⟦_⟧ₒ-recurse : ∀ {i A} → List (OC i A) → Configuration → List (V A)
  ⟦_⟧ₒ-recurse : ∀ {i} {Option : 𝔽} → 𝔼-Semantics (List ∘ V) (Configuration Option) (List ∘ OC Option i)
  ⟦ es ⟧ₒ-recurse c =
    catMaybes -- Keep everything that was chosen to be included and discard all 'nothing' values occurring from removed options.
    (map (flip ⟦_⟧ₒ c) es)

  ⟦ a -< es >- ⟧ₒ c = just (cons mkArtifact (a At.-< ⟦ es ⟧ₒ-recurse c >-))
  ⟦ O ❲ e ❳ ⟧ₒ c = if c O then ⟦ e ⟧ₒ c else nothing
```

And now for the semantics of well-formed option calculus which just reuses the semantics of option calculus but we have the guarantee of the produced variants to exist.
```agda
  ⟦_⟧ : ∀ {i : Size} {Option : 𝔽} → 𝔼-Semantics V (Configuration Option) (WFOC Option i)
  ⟦ Root a es ⟧ c = cons mkArtifact (a At.-< ⟦ es ⟧ₒ-recurse c >-)

  WFOCL : ∀ {i : Size} (Option : 𝔽) → VariabilityLanguage V
  WFOCL {i} Option = ⟪ WFOC Option i , Configuration Option , ⟦_⟧ ⟫
```

-- ### Option calculus is unsound

-- Option calculus is unsound by construction because it is not a variability language over variants V
-- but over Maybe ∘ V, i.e., an option calculus expression might be configured to something else which
-- is not a variant (i.e., nothing).
-- TODO: Maybe we can still explicitly construct the `Unsound` predicate.

-- ### Well-formed option calculus is sound

```agda
-- TODO (Probably prove via soundness-by-expressiveness (done) and soundness of 2CC (todo))
```


```agda
open import Data.Fin using (zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product   using (_,_; ∃-syntax; ∄-syntax)
open import Util.Existence using (_,_)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

module _ {Option : 𝔽} where
```

## Incompleteness

We prove incompleteness by showing that there exists at least one set of variants that cannot be described by option calculus.
In particular, any set of variants that includes two entirely distinct variants cannot be expressed because options cannot encode constraints such as alternatives in choice calculus.
As our counter example, we use the set `{0, 1}` as our variants:
```agda
  -- TODO: Can this be generalized to other types of variants as well?
  module IncompleteOnRose where
    open import Framework.Variants using (Rose; Artifact∈ₛRose)
    open import Framework.VariantMap (Rose ∞) (ℕ , ℕ._≟_)
    open import Framework.Properties.Completeness (Rose ∞) using (Incomplete)
    open Sem (Rose ∞) Artifact∈ₛRose

    variant-0 = rose-leaf {A = (ℕ , ℕ._≟_)} 0
    variant-1 = rose-leaf {A = (ℕ , ℕ._≟_)} 1
    -- variant-0 = cons mkArtifact (At.leaf 0)
    -- variant-1 = cons mkArtifact (At.leaf 1)

    variants-0-and-1 : VMap 1
    variants-0-and-1 zero = variant-0
    variants-0-and-1 (suc zero) = variant-1
```
We stick to this concrete counter example instead of formulating the set of unrepresentable variants here to make the proof not more complicated than necessary.

We now prove that any well-formed option calculus expression `e` cannot be configured to `0` and `1` at the same time. The reason is that the expression `e` always has a domain element at the top. This element is always included in the variant and cannot simultaneously be `0` and `1`.
So we show that given an expression `e`, a proof that `e` can be configured to `0`, and a proof that `e` can be configured to `1`, we eventually conclude falsehood.
```agda
    does-not-describe-variants-0-and-1 :
      ∀ {i : Size}
      → (e : WFOC Option i (ℕ , ℕ._≟_))
      → ∃[ c ] (variant-0 ≡ ⟦ e ⟧ c)
      → ∄[ c ] (variant-1 ≡ ⟦ e ⟧ c)
    -- If e has 0 as root, it may be configured to 0 but never to 1.
    does-not-describe-variants-0-and-1 (Root 0 es) ∃c→v0≡⟦e⟧c ()
    -- if e has a number larger than 1 at the top, it cannot be configured to yield 0.
    does-not-describe-variants-0-and-1 (Root (suc n) es) ()
```

Finally, we can conclude incompleteness by showing that assuming completeness yields a contradiction using our definition above.
We pattern match on the assumed completeness evidence to unveil the expression `e` and the proofs that it can be configured to `0` and `1`.
```agda
    OC-is-incomplete : Incomplete (WFOCL Option)
    OC-is-incomplete assumed-completeness with assumed-completeness variants-0-and-1
    ... | e , ∀n→∃c→vn≡⟦e⟧ , _ = does-not-describe-variants-0-and-1 e (∀n→∃c→vn≡⟦e⟧ zero) (∀n→∃c→vn≡⟦e⟧ (suc zero))
```

**This is an important result!**
It shows that we need at least some constraints to be complete.
This is a justification for choice calculus defining variability annotations with constraints (being alternative) instead of being pure annotations.
Another way is to enrich the annotation language, for example using propositional logic.

## Utility

```agda
  oc-leaf : ∀ {i : Size} {A : 𝔸} → atoms A → OC Option (↑ i) A
  oc-leaf a = a -< [] >-

  -- alternative name that does not require writing tortoise shell braces
  opt : ∀ {i : Size} {A : 𝔸} → Option → OC Option i A → OC Option (↑ i) A
  opt O = _❲_❳ O

  singleton : ∀ {i : Size} {A : 𝔸} → atoms A → OC Option i A → OC Option (↑ i) A
  singleton a e = a -< e ∷ [] >-

  open import Util.Named

  all-oc : Bool → Configuration Option
  all-oc b _ = b

  allyes-oc : Named (Configuration Option)
  allyes-oc = all-oc true called "all-yes"

  allno-oc : Named (Configuration Option)
  allno-oc = all-oc false called "all-no " --space intended for nicer printing lol
```

## Show

```agda
open String using (_++_; intersperse)
open import Function using (_∘_)

module Show (Option : 𝔽) (print-opt : Option → String) where
  show-oc : ∀ {i : Size} → OC Option i (String , String._≟_) → String
  show-oc (s -< [] >-) = s
  show-oc (s -< es@(_ ∷ _) >-) = s ++ "-<" ++ (intersperse ", " (map show-oc es)) ++ ">-"
  show-oc (O ❲ e ❳) = print-opt O ++ "❲" ++ show-oc e ++ "❳"

  show-wfoc : ∀ {i : Size} → WFOC Option i (String , String._≟_) → String
  show-wfoc = show-oc ∘ forgetWF
```
