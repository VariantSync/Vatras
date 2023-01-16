# Core Choice Calculus

## Options

For termination checking, we have to use sized types (i.e., types that are bounded by a certain size).
We use sizes to constrain the maximum tree-depth of an expression.
```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.CC where
```

## Imports
```agda
-- Imports from Standard Library
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat
  using (ℕ; zero; suc; NonZero)
open import Data.Product
  using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String
  using (String; _++_)
open import Function
  using (_∘_; flip)
open import Size
  using (Size; Size<_; ↑_; ∞; _⊔ˢ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Imports of own modules
open import Lang.Annotation.Dimension using (Dimension; _==_)
open import Translation.Translation
  -- Names
  using (VarLang; ConfLang; Domain; Semantics)
  -- Relations of expression in a variability language
  using (_,_⊢_≈_; _,_⊢_⊆_; _,_⊢_≚_; ≈→≚)
  -- Relations of expression in two variability languages
  using (_,_and_,_⊢_⊆_; _,_and_,_⊢_≚_)
  -- Relations between variability languages
  using (_,_is-as-expressive-as_,_)
  -- Translations
  using (Translation; conf; fnoc)
  -- Translation properties
  using (_⊆-via_; _⊇-via_; _is-variant-preserving; _is-semantics-preserving; translation-proves-variant-preservation)
open import Extensionality
  using (extensionality; _embeds-via_)
  renaming (map-cong-≡ to mapl-cong-≡; map-cong-≗-≡ to mapl-cong-≗-≡)
```

## Syntax

Let's define core choices calculus as defined in Eric's phd thesis.
To prove that our functions terminate and thus prove that our proofs are not self-referential and sound inductions, we extend the definition of the core choice calculus by a size parameter.
The size parameter is an upper bound for nesting depth of a choice calculus expression.
In the constructors, j denotes an upper bound for the nesting depth of children.
(Martin and Eric established a similar bound for termination checking in their TOSEM paper (p.17).)
```agda
Tag : Set
Tag = ℕ

data CC : VarLang where
  Artifact : ∀ {i : Size} {j : Size< i} {A : Domain} →
    A → List (CC j A) → CC i A
  _⟨_⟩ : ∀ {i : Size} {j : Size< i} {A : Domain} →
    Dimension → List⁺ (CC j A) → CC i A
```

From this slightly more complex definition, we can obtain the original definition of choice calculus without an upper bound for the expression depth.
In the original definition, we neither care for nor know the depth of an expression.
So we just pick infinity as a proper upper bound because we speak about expressions of arbitrary depth.
```agda
CCC : Domain → Set
CCC = CC ∞
```

Smart constructors for plain artifacts.
Any upper bound is fine but we are at least 1 deep.
```agda
leaf : ∀ {i : Size} {A : Domain} → A → CC (↑ i) A
leaf a = Artifact a []

leaves : ∀ {i : Size} {A : Domain} → List⁺ A → List⁺ (CC (↑ i) A)
leaves = mapl⁺ leaf

upcast : ∀ {i : Size} {j : Size< i} {A : Domain} → CC j A → CC i A
upcast e = e
```

## Semantics

Choice calculus has denotational semantics, introduced by Eric in the TOSEM paper and his PhD thesis.
Semantics for choice calculus can be defined in different ways.
In his phd thesis, Eric defined the semantics to be the set of all variants described by the expression.
So the semantic domain was a set of choice calculus expressions without any choices.
We can encode a choice calculus expression without choices at the type level:
```agda
open import SemanticDomains using (Variant; Artifactᵥ)
```

An equivalent definition of semantics produces a configuration function `Config → Variant` that generates variants from configurations.
This definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags, according to Eric's phd thesis:
```agda
Configuration : ConfLang
Configuration = Dimension → Tag
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to introduce complex error handling and we cannot easily define a configuration to only produce tags within ranges.

```agda
open import Data.Fin.Base using (Fin)
open import AuxProofs using (minFinFromLimit)

{-|
Clamps a tag at the given length.
Takes a length n as implicit first argument and a proof that this length is positive as second argument.
In case the given tag is smaller than the given length, the tag is returned, otherwise the length - 1.
Returns an index which is proven to be smaller than the given length.
-}
clampTagWithin : {n : ℕ} → {NonZero n} → Tag → Fin n
clampTagWithin {suc n} {nz} = minFinFromLimit n

-- Selects the alternative at the given tag.
-- Agda can implicitly prove that the length of the list is positive, because it is a non-empty list, and by type inference, it supplies the list length to clampWithin.
choice-elimination : {A : Domain} → Tag → List⁺ A → A
choice-elimination t alts⁺ = lookup (toList alts⁺) (clampTagWithin t)

{-|
Semantics of core choice calculus.
The semantic domain is a function that generates variants given configurations.
-}
⟦_⟧ : Semantics CC Configuration
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ alternatives ⟩ ⟧ c = ⟦ choice-elimination (c D) alternatives ⟧ c
```

## Properties

Some transformation rules
```agda
-- unary choices are mandatory
D⟨e⟩≈e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    --------------------------
  → CC , ⟦_⟧ ⊢ D ⟨ e ∷ [] ⟩ ≈ e
D⟨e⟩≈e = refl

-- other way to prove the above via variant-equivalence

D⟨e⟩⊂̌e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    --------------------------
  → CC , ⟦_⟧ ⊢ D ⟨ e ∷ [] ⟩ ⊆ e
D⟨e⟩⊂̌e config = ( config , refl )

e⊂̌D⟨e⟩ : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    --------------------------
  → CC , ⟦_⟧ ⊢ e ⊆ D ⟨ e ∷ [] ⟩
e⊂̌D⟨e⟩ config = ( config , refl )

D⟨e⟩≚e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    --------------------------
  → CC , ⟦_⟧ ⊢ D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e {i} {A} {e} {D} = D⟨e⟩⊂̌e {i} {A} {e} {D} , e⊂̌D⟨e⟩ {i} {A} {e} {D}
```

Finally, we get the alternative proof of `D ⟨ e ∷ [] ⟩ ≚ e`:
```agda
D⟨e⟩≚e' : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → CC , ⟦_⟧ ⊢ D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e' {i} {A} {e} {D} =
  ≈→≚ {↑ i} {i}
      {CC} {Configuration} {⟦_⟧} {A}
      {D ⟨ e ∷ [] ⟩} {e}
      (D⟨e⟩≈e {i} {A} {e} {D})
```

Finally, let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda

-- Any upper bound is fine but we are at least 2 deep.
cc_example_walk : ∀ {i : Size} → CC (↑ ↑ i) String
cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

cc_example_walk_zoom : Variant String
cc_example_walk_zoom = ⟦ cc_example_walk ⟧ (λ {"Ekko" → 0; _ → 0})
```

Running this program shows that `cc_example_walk_zoom` indeed evaluates to the String `zoom`.
But we can also prove it:
```agda
_ : cc_example_walk_zoom ≡ Artifactᵥ "zoom" []
_ = refl
```

## Utility

```agda
-- get all dimensions used in a CC expression
open Data.List using (concatMap)

dims : ∀ {i : Size} {A : Set} → CC i A → List Dimension
dims (Artifact _ es) = concatMap dims es
dims (D ⟨ es ⟩) = D ∷ concatMap dims (toList es)
```

## Show

```agda
show : ∀ {i : Size} → CC i String → String
show (Artifact a []) = a
show (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl show es)) ++ ">-"
show (D ⟨ es ⟩) = D ++ "<" ++ (Data.String.intersperse ", " (toList (mapl⁺ show es))) ++ ">"
```
