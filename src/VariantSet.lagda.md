# Data Type to Describe Sets of Variants

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module VariantSet where
```

## Imports

```agda
open import Size using (∞)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (_∷_)

open import Definitions using (Domain; ConfLang)
open import SemanticDomain using (Variant; Artifactᵥ)

open import Lang.CCC using (CCC; Artifact; _⟨_⟩)
```

## Question to Parisa

Regarding the definition of completness in Agda we looked at yesterday, I could need some advice. In particular, regarding you expertise in Coq: _How would you model subsets in (dependent) type theory_?

The idea of completeness was to say: Given any set of variants (e.g., three concrete variants such as `{1, 2, 3}`), then we can build an expression that describes exactly this set (e.g., `D ⟨1, 2, 3 ⟩` in choice calculus). Thus in Agda, we need a way to describe such a "set of variants".

Following the idea of propositions as types, we model sets as types. But the type `Variant A` models the set of _all_ variants in a domain `A`, despite us being interested in just a subset, such as `{1, 2, 3}`. So far I used a list of variants to represent such a subset:
```agda
set-as-list : List (Variant ℕ)
set-as-list = (Artifactᵥ 1 []) ∷ (Artifactᵥ 2 []) ∷ (Artifactᵥ 3 []) ∷ []
```
This is a bit fiddly in proofs but works.

Another idea I had, was abstracting that list and using a function that indexes variants. This follows the idea of how we actually define sets of variants in the semantics `Expression → Configuration → Variant` of variability languages. The idea is to take a set that is exactly the size as the set of variants we want to describe (`3` in our example here). In Agda, and I think also in Coq, that data type is `Fin n` where `n ∈ ℕ`. Then, define a subset of variants as a function `Fin n → Variant A` that basically _selects_ the variants we want to have from the overall set of variants `Variant A`:
```agda
set-as-function : Fin 3 → Variant ℕ
set-as-function           zero   = Artifactᵥ 1 []
set-as-function      (suc zero)  = Artifactᵥ 2 []
set-as-function (suc (suc zero)) = Artifactᵥ 3 []
```

In fact, the denotational semantics of any variability language is a set of variants. So any description for a set of variants in Agda we choose will itself again be a variability language. For instance, a list of variants (as we currently use for the definition of completeness) is also a variability langage: The expressions are lists, the configurations are natural numbers, configuring a list is selecting an element. And indeed, we could also use choice calculus as a description for sets of variants that way:
```agda
set-as-choice : CCC ∞ ℕ
set-as-choice = "Foo" ⟨ (Artifact 1 []) ∷ (Artifact 2 []) ∷ (Artifact 3 []) ∷ [] ⟩
```
which is the whole point behind choice calculus apart from sharing.

So the actual task here boils down to finding "the simplest" variablity language that we can agree on as a canonical and basic definitions and that makes the proofs simple and theorems believable. I guess the simplest way would be "a set of variants" itself but, yeah, how to say that in type theory?

My bet is currently on Fin. On the other hand, we already have to proves done on lists (to prove completeness-by-expressiveness) and we can use the Agda stl definitions for `ANy` and `All` that are basically _OR_ and _AND_ over lists.

Moreover, the have to ensure that variant subsets are non-empty in our definition of completeness (which currently allows for empty subsets). A variability language should not be able to encode 0 variants in an expression. This would require an empty expression which does not make sense.


## Definitions

as selector function
```agda
VariantSet : Domain → ℕ → Set
VariantSet A n = Fin n → Variant A
```

