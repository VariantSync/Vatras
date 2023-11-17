```agda
{-# OPTIONS --sized-types #-}

module Framework.V2.TODO where

-- open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq
open import Level using (0ℓ)

open import Framework.V2.Definitions
import Framework.V2.Constructs.Choices as Chc
open Chc.VLChoice₂ renaming (Syntax to 2Choice)

open import Framework.V2.Constructs.NestedChoice using (NestedChoice)
```

# TODOs for Framework V.2

## Goal Statement

Prove for all of the following languages whether they are complete, sound, and how expressive they are

| Language | Modelled in V1? | Modelled in V2? | Completeness | Soundness |
|----------|-----------------|-----------------|--------------|-----------|
| CCC | yes | no | yes | ? |
| BCC | yes | no | ? | ? |
| OC | yes | no | ? | no (implicit so far) |
| WFOC | yes | no | no | ? |
| Feature Algebra | no | no | ? | ? |
| (2ADTs) | yes | yes | ? | ? |
| (Variation Tree) | no | no | ? | ? |
| (Gruler languages) | no | yes? | ? | ? |

## Issues

Next Issue No: 12


### [3] Embed Variants

Similar to [2], show that any language that
- has `Artifact`s can encode a single given `Variant`
- has `ParallelComposition` and `Leaf` can encode any given `GrulerVariant`
We need this to prove completeness of languages later.

### [5] Generalize Completeness and Soundness Proofs of CCC in Framework V1

requires [3]

In the first framework version, we have proven that CCC is complete, by

1. showing that a list of variants (`VariantList`) is sound and complete
2. showing that CCC can encode any VariantList.

Generalized this proof to any langauge with artifacts and n-ary choices.

### [6] Conclude Completeness of BCC

By transitivity, use [5] to conclude that any language with binary choices and artifacts is complete.

### [7] Prove Soundness of of CCC

So far we have proven that VariantLists are sound.
We would like to conclude soundness of other languages as well.
This can be done for example, by showing that VariantList is at least as expressive as another language.
Figure out which proof path would be the easiest here.

Can we conclude soundness for classes of languages instead of just individual langauges, similar as we can do for completeness?
I guess we cannot say something like "any language with choices and artifacts is sound" because there could be more constructors that may cause unsoundness.
Maybe we can say: "Any langauge with at most constructors X Y Z"?

Anway: Our goal is to prove soundness of CCC or a similar language and then conclude soundness for other languages by transitivity of our compilers (including well-formed option calculus).

### [8] Implement Compositional Variability

So far, we only covered annotative variability.
However, variability may also be implemented compositionally.
One language for compositional variability is the feature algebra by Apel et al. [ALMK:SCP10].
Here, a variant is _composed_ by superimposition of different trees.
That is, a feature is represented by a path from the root to a terminal node.
By composing such paths, trees are obtained, which represent variants.

To have to investigate
1. whether our framework can model this algebra
2. whether our framework can compare this algebra with other variability language.

If we can do both, then we can compare annotative _and_ compositional variability, strengthening our evaluation by miles.

### [9] Model Options in Framework V2

Currently, we have modelled options in terms of option calculus in Framework V1.
Is there any benefit in modelling options as individual constructs?
Can we make interesting theorems over a range of option calculi?

It would be cool for example, if we could reason on Variation Trees (Option + Artifact + Choice) and Option Calculus (Option + Artifact) at once.

### [10] Generalize Translation OC→BCC

Since OC can be converted to BCC, it can be converted to any langauge with binary choices and artifacts.
Generalizing this, would allow us to generalize the concluded expressiveness statement:
Any language with binary choices and artifacts is at least as expressive as OC.

### [11] Expressiveness of Constructs

Can we reasonably model expressiveness for constructs and not just whole langauges?
[10] is already a start into a direction, where we dont compare the expressiveness of languages directly,
but of classes of languages, quantified by their constructors.
Maybe thats all we need.
Maybe this issue is the goal towards syntactic comparisons instead of semantic ones:
1. Compare semantic expressiveness of constructs.
2. Compare size if syntax of constructs.

Or something like this.

## Closed Issues

### [1] Generalize Levels

Started on branch `generalize-levels` but has to be continued. We need this at several places to simplify or refactor things.

### [2] Embed NestedChoice

Prove that we can embed a NestedChoice into any variability language that has binary choices.
Essentially, implement a function:

```agda
postulate
  -- When levels are generalized, we do not have to specifically use 0ℓ here.
  embed : ∀ {V F S A} {i}
    → (Γ : VariabilityLanguage V F S)
    → F ⊢ 2Choice ∈ₛ Expression Γ
    → NestedChoice F i (Expression Γ A)
    → Expression Γ A
```

and prove that semantics is preserved.

The idea is the we can express a nested choice in any language that has binary choices.
Once this proof is complete, we can by transitivity, encode an n-ary choice into any language that has binary choices.

```agda
{-|
assume: Choice₂ ∈ₛ L₂
Choiceₙ L₁ ── convert ─⟶ 2ADT L₁
                          |
                          | map compile
                          ↓
                        2ADT (L₂ A)
                          |
                          | embed
                          ↓
                          L₂
-}
```

### [4] Replace NestedChoice by 2ADT

Both languages have the same syntax, so we could just use 2ADT where we currently use NestedChoice.
