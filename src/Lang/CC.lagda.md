# Choice Calculus in Agda

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
open import Data.String
  using (String; _++_)
open import Function
  using (_∘_; flip)
open import Size
  using (Size; Size<_; ↑_; ∞)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Imports of own modules
open import Extensionality
  using (extensionality)
  renaming (map-cong-≡ to mapl-cong-≡; map-cong-≗-≡ to mapl-cong-≗-≡)
```

## Core Choice Calculus

Let's define core choices calculus as defined in Eric's phd thesis.
To prove that our functions terminate and thus prove that our proofs are not self-referential and sound inductions, we extend the definition of the core choice calculus by a size parameter.
The size parameter is an upper bound for nesting depth of a choice calculus expression.
In the constructors, j denotes an upper bound for the nesting depth of children.
(Martin and Eric established a similar bound for termination checking in their TOSEM paper (p.17).)
```agda
Dimension : Set
Dimension = String

Tag : Set
Tag = ℕ

data CC (i : Size) (A : Set) : Set where
  Artifact : ∀ {j : Size< i} →
    A → List (CC j A) → CC i A
  _⟨_⟩ : ∀ {j : Size< i} →
    Dimension → List⁺ (CC j A) → CC i A
```

From this slightly more complex definition, we can obtain the original definition of choice calculus without an upper bound for the expression depth.
In the original definition, we neither care for nor know the depth of an expression.
So we just pick infinity as a proper upper bound because we speak about expressions of arbitrary depth.
```agda
CoreCC : Set → Set
CoreCC = CC ∞
```

### Helpful Functions for Later

Equality of dimensions:
```agda
import Data.String.Properties
open import Relation.Binary.Definitions using (Decidable)
--open import Relation.Nullary.Decidable using (isYes; yes)

_dim-≟_ : Decidable (_≡_)
_dim-≟_ = Data.String.Properties._≟_

_dim-==_ : Dimension → Dimension → Bool
_dim-==_ = Data.String.Properties._==_
```

Smart constructors for plain artifacts.
Any upper bound is fine but we are at least 1 deep.
```agda
leaf : ∀ {i : Size} {A : Set} → A → CC (↑ i) A
leaf a = Artifact a []

leaves : ∀ {i : Size} {A : Set} → List⁺ A → List⁺ (CC (↑ i) A)
leaves = mapl⁺ leaf
```

### Semantics

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
Configuration : Set
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
choice-elimination : {A : Set} → Tag → List⁺ A → A
choice-elimination t alts⁺ = lookup (toList alts⁺) (clampTagWithin t)

{-|
Semantics of core choice calculus.
The semantic domain is a function that generates variants given configurations.
-}
⟦_⟧ : ∀ {i : Size} {A : Set} → CC i A → Configuration → Variant A
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ alternatives ⟩ ⟧ c = ⟦ choice-elimination (c D) alternatives ⟧ c
```

Semantic equivalence means that the same configurations yield the same variants:
```agda
_≈_ : ∀ {i j : Size} {A : Set}
  → (a : CC i A) → (b : CC j A) → Set
a ≈ b = ⟦ a ⟧ ≡ ⟦ b ⟧
infix 5 _≈_
```

Semantic equivalence `≈` inherits all properties from structural equality `≡` because it is just an alias.
In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence as stated in the choice calculus TOSEM paper.

Obviously, syntactic equality (or rather structural equality) implies semantic equality:
```agda
≡→≈ : ∀ {i : Size} {A : Set} {a b : CC i A}
  → a ≡ b
    -----
  → a ≈ b
≡→≈ eq rewrite eq = refl
```

Some transformation rules
```agda
-- unary choices are mandatory
D⟨e⟩≈e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≈ e
D⟨e⟩≈e = refl
```

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence.
Each variant that can be derived from the first CC expression, can also be derived from the second CC expression and vice versa.
We thus first describe the variant-subset relation ⊂̌ and then define variant-equality as a bi-directional subset.

For the variant-subset relation, we want to express the following, given two expressions `e₁` and `e₂`:

       Every variant described by e₁ is also described by e₂.
    ⇔ For all variants v in the image of ⟦ e₁ ⟧
       there exists a configuration c
       such that ⟦ e₂ ⟧ c ≡ v.
    ⇔ For all configurations c₁
       there exists a configuration c₂
       such that ⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂.

```agda
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)

-- Beware! This symbol renders different on Github. The v should be on top of ⊂ but on Github is next to it.
-- So don't be confused in case the v appears on top of a character next to ⊂.
-- Unicode for ⊂̌ is \sub\v
_⊂̌_ : ∀ {i j : Size} {A : Set}
  → (e₁ : CC i A) → (e₂ : CC j A) → Set
e₁ ⊂̌ e₂ = ∀ (c₁ : Configuration) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
infix 5 _⊂̌_

-- some properties
-- _⊂̌_ is not symmetric

⊂̌-refl : ∀ {i : Size} {A : Set} {e : CC i A}
    -----
  → e ⊂̌ e
⊂̌-refl c = c , refl

⊂̌-trans : ∀ {i j k : Size} {A : Set} {e₁ : CC i A} {e₂ : CC j A} {e₃ : CC k A}
  → e₁ ⊂̌ e₂
  → e₂ ⊂̌ e₃
    -------
  → e₁ ⊂̌ e₃
⊂̌-trans x y c₁ =
  -- this somehow resembles the implementation of bind >>= of state monad
  let (c₂ , eq₁₂) = x c₁
      (c₃ , eq₂₃) = y c₂
  in c₃ , Eq.trans eq₁₂ eq₂₃

-- Variant-preserving equality of CC is structural equality of all described variants.
-- (It is not semantic equality of variants because we do not the semantics of
-- the object language!)
-- Unicode for ≚ is \or=
_≚_ : ∀ {i j : Size} {A : Set}
  → (e₁ : CC i A) → (e₂ : CC j A) → Set
e₁ ≚ e₂ = (e₁ ⊂̌ e₂) × (e₂ ⊂̌ e₁)
infix 5 _≚_

-- properties of variant-preserving equivalence
≚-sym : ∀ {i j : Size} {A : Set} {e₁ : CC i A} {e₂ : CC j A}
  → e₁ ≚ e₂
    -------
  → e₂ ≚ e₁
≚-sym (e₁⊂̌e₂ , e₂⊂̌e₁) = e₂⊂̌e₁ , e₁⊂̌e₂

≚-trans : ∀ {A : Set} {i j k : Size} {e₁ : CC i A} {e₂ : CC j A} {e₃ : CC k A}
  → e₁ ≚ e₂
  → e₂ ≚ e₃
    -------
  → e₁ ≚ e₃
≚-trans {A} {i} {j} {k} {e₁} {e₂} {e₃} (e₁⊂̌e₂ , e₂⊂̌e₁) (e₂⊂̌e₃ , e₃⊂̌e₂) =
    ⊂̌-trans {i} {j} {k} {A} {e₁} {e₂} {e₃} e₁⊂̌e₂ e₂⊂̌e₃
  , ⊂̌-trans {k} {j} {i} {A} {e₃} {e₂} {e₁} e₃⊂̌e₂ e₂⊂̌e₁
```

As an example, we now prove `D ⟨ e ∷ [] ⟩ ≚ e`.
```agda
D⟨e⟩⊂̌e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ⊂̌ e
D⟨e⟩⊂̌e config = ( config , refl )

e⊂̌D⟨e⟩ : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → e ⊂̌ D ⟨ e ∷ [] ⟩
e⊂̌D⟨e⟩ config = ( config , refl )

D⟨e⟩≚e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e {i} {A} {e} {D} = D⟨e⟩⊂̌e {i} {A} {e} {D} , e⊂̌D⟨e⟩ {i} {A} {e} {D}
```

In fact, we already have proven `D ⟨ e ∷ [] ⟩ ≈ e` earlier, from which `D ⟨ e ∷ [] ⟩ ≚ e` follows:
```agda
-- Semantic equivalence implies variant equivalence.
≈→⊂̌ : ∀ {i j : Size} {A : Set} {a : CC i A} {b : CC j A}
  → a ≈ b
    -----
  → a ⊂̌ b
-- From a≈b, we know that ⟦ a ⟧ ≡ ⟦ b ⟧. To prove subset, we have to show that both sides produce the same variant for a given configuration. We do so by applying the configuration to both sides of the equation of a≈b.
≈→⊂̌ a≈b config = config , Eq.cong (λ ⟦x⟧ → ⟦x⟧ config) a≈b

-- Semantic equivalence implies variant equivalence.
≈→≚ : ∀ {i j : Size} {A : Set} {a : CC i A} {b : CC j A}
  → a ≈ b
    -----
  → a ≚ b
≈→≚ {i} {j} {A} {a} {b} a≈b =
    ≈→⊂̌ {i} {j} {A} {a} {b} a≈b
  , ≈→⊂̌ {j} {i} {A} {b} {a} (Eq.sym a≈b)
```

Finally, we get the alternative proof of `D ⟨ e ∷ [] ⟩ ≚ e`:
```agda
D⟨e⟩≚e' : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e' {i} {A} {e} {D} =
  ≈→≚ {↑ i} {i} {A} {D ⟨ e ∷ [] ⟩} {e} (D⟨e⟩≈e {i} {A} {e} {D})
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

## Binary Normal Form

In the following we introduce normal forms for choice calculus expressions.
We express each normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.
Our goal is to prove that every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.

As for choice calculus, `i` is an upper bound for the depth of the expression tree.
```agda
data CC₂ (i : Size) (A : Set) : Set where
  Artifact₂ : {j : Size< i} →
    A → List (CC₂ j A) → CC₂ i A
  _⟨_,_⟩₂ : {j : Size< i} →
    Dimension → CC₂ j A → CC₂ j A → CC₂ i A
```

The semantics of binary normal form is essentially the same as for n-ary choice calculus.
We define the semantics explicitly though because of two reasons:

1. Specializing the semantics to the binary case gives rise to further simplifications and transformation rules.
2. Defining binary semantics explicitly allows us to prove that a conversion from and to binary normal form is semantics preserving.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also ok but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Tag₂ : Set
Tag₂ = Bool

left  = true
right = false

Configuration₂ : Set
Configuration₂ = Dimension → Tag₂

⟦_⟧₂ : ∀ {i : Size} {A : Set} → CC₂ i A → Configuration₂ → Variant A
⟦ Artifact₂ a es ⟧₂ c = Artifactᵥ a (mapl (flip ⟦_⟧₂ c) es)
⟦ D ⟨ l , r ⟩₂ ⟧₂ c = ⟦ if (c D) then l else r ⟧₂ c
```

Semantic equivalence for binary choice calculus:
```agda
_≈₂_ : ∀ {i j : Size} {A : Set}
  → (a : CC₂ i A) → (b : CC₂ j A) → Set
a ≈₂ b = ⟦ a ⟧₂ ≡ ⟦ b ⟧₂
infix 5 _≈₂_
```

Some transformation rules:
```agda
open AuxProofs using (if-idemp; if-cong)
open Data.List using ([_])

cc₂-idemp : ∀ {i : Size} {A : Set} {D : Dimension} {e : CC₂ i A}
    ----------------
  → D ⟨ e , e ⟩₂ ≈₂ e
cc₂-idemp {i} {A} {D} {e} = extensionality (λ c →
  ⟦ D ⟨ e , e ⟩₂ ⟧₂ c             ≡⟨⟩
  ⟦ if (c D) then e else e ⟧₂ c  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧₂ c) (if-idemp (c D)) ⟩
  ⟦ e ⟧₂ c                       ∎)

-- Sharing of equal prefixes in sub-expressions
-- Note: This is hard to generalize to Artifact₂'s with multiple children because
--       we cannot put these children below the choice directly. Instead we would have
--       to introduce empty artifacts that do not represent expression in the object language but
--       rather containers in the meta-language. Maybe it would make sense to generalize choice
--       calculus to have lists of lists of children in choices instead of exactly one subtree per alternative.
cc₂-prefix-sharing : ∀ {i : Size} {A : Set} {D : Dimension} {a : A} {x y : CC₂ i A}
  → D ⟨ Artifact₂ a [ x ] , Artifact₂ a [ y ] ⟩₂ ≈₂ Artifact₂ a [ D ⟨ x , y ⟩₂ ]
cc₂-prefix-sharing {_} {_} {D} {a} {x} {y} = extensionality (λ c →
  begin
    ⟦ D ⟨ Artifact₂ a [ x ] , Artifact₂ a [ y ] ⟩₂ ⟧₂ c
  ≡⟨⟩
    ⟦ if (c D) then (Artifact₂ a [ x ]) else (Artifact₂ a [ y ] ) ⟧₂ c
  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧₂ c) (if-cong (c D) (λ {v → Artifact₂ a [ v ]}) ) ⟩
    ⟦ Artifact₂ a [ if (c D) then x else y ] ⟧₂ c
  ≡⟨⟩
    ⟦ Artifact₂ a [ D ⟨ x , y ⟩₂ ] ⟧₂ c
  ∎)
```

## Semantic Equivalence of Choice Calculus and Binary Normal Form

Now that we've introduced the binary normal form at the type level, we want to show that (1) any n-ary choice calculus expression can be transformed to binary normal form, and (2) any binary normal form expression is a choice calculus expression. Therefore, we construct the respective transformations in the following.

To prove that both transformations are valid, we define semantic equivalence between a binary and an n-ary choice calculus expression.
Semantic equivalence between a binary and n-ary choice calculus expression cannot be expressed directly because the semantics of binary and n-ary choice calculus use different types of configurations.
Yet, we can compare the set of described variants in terms of variant-preserving equivalence.
Thus, both expressions are considered semantically equal if they yield the same variants for all configurations.
```agda
{-
We use a formulation similar to the one for variant equivalence for n-ary choice calculus.
Equivalence is subset in both directionss.
-}
_₂⊂̌ₙ_ : ∀ {i j : Size} {A : Set}
  → CC₂ i A → CC j A → Set
cc₂ ₂⊂̌ₙ ccₙ = ∀ (c₂ : Configuration₂) → ∃[ c ] (⟦ cc₂ ⟧₂ c₂ ≡ ⟦ ccₙ ⟧ c)

_ₙ⊂̌₂_ : ∀ {i j : Size} {A : Set}
  → CC i A → CC₂ j A → Set
ccₙ ₙ⊂̌₂ cc₂ = ∀ (c : Configuration) → ∃[ c₂ ] (⟦ cc₂ ⟧₂ c₂ ≡ ⟦ ccₙ ⟧ c)

_₂≚ₙ_ : ∀ {i j : Size} {A : Set}
  → CC₂ i A → CC j A → Set
cc₂ ₂≚ₙ ccₙ = (cc₂ ₂⊂̌ₙ ccₙ) × (ccₙ ₙ⊂̌₂ cc₂)

-- sugar for inverse direction
_ₙ≚₂_ : ∀ {i j : Size} {A : Set}
  → CC i A → CC₂ j A → Set
ccₙ ₙ≚₂ cc₂ = cc₂ ₂≚ₙ ccₙ
```

### Binary to N-ary Choice Calculus

We start with the second task: Converting a choice calculus expression of which we know at the type level that it is in binary normal form, back to n-ary choice calculus.
It will still be an expression in binary normal form but we will lose that guarantee at the type level.
```agda
{- |
Converts a binary choice calculus expression to a core choice calculus expression.
The resulting expression is syntactically equivalent and thus still in binary normal form.
We only drop the knowledge of being in binary normal form at the type level.
-}
toCC : ∀ {i : Size} {A : Set} → CC₂ i A → CC i A
toCC (Artifact₂ a es) = Artifact a (mapl toCC es)
toCC (D ⟨ l , r ⟩₂) = D ⟨ (toCC l) ∷ (toCC r) ∷ [] ⟩

-- Conversion of configurations.
{-
When converting configurations for toCC, we have decide on a possible mapping between booleans and natural numbers.
We chose a mapping that preserves semantics:
true means going left in a binary expression, as does 0 in an n-ary choice calculus expression.
Analoguous for false.
-}
asTag : Tag₂ → Tag
asTag true  = 0
asTag false = 1

asTag₂ : Tag → Tag₂
asTag₂ zero    = true
asTag₂ (suc n) = false

{- |
Convert binary configuration to n-ary configuration.
Only valid for our translation from CC₂ to CC.
-}
toNaryConfig : Configuration₂ → Configuration
toNaryConfig c₂ = asTag ∘ c₂

{- |
Convert n-ary configuration to binary.
Only valid for our translation from CC₂ to CC.
-}
toBinaryConfig : Configuration → Configuration₂
toBinaryConfig c = asTag₂ ∘ c
```

And now for the proofs.
```agda
CC₂→CC-left : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → e ₂⊂̌ₙ toCC e

CC₂→CC-right : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → toCC e ₙ⊂̌₂ e

-- Main theorem for drawing an arrow from CC₂ to CC.
CC₂→CC : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → e ₂≚ₙ toCC e
CC₂→CC {i} {A} {e} =
    CC₂→CC-left  {i} {A} {e}
  , CC₂→CC-right {i} {A} {e}
```

#### Proof of the left side

```agda
-- helper function that tells us that the existing n-ary configuration, given a binary configuration, is toNaryConfig c₂. That basically unwraps the ∃ and avoids to write pairs all the time.
CC₂→CC-left-toNaryConfig : ∀ {i : Size} {A : Set}
  → ∀ (e : CC₂ i A)
  → ∀ (c₂ : Configuration₂)
    -------------------------------------
  → ⟦ e ⟧₂ c₂ ≡ ⟦ toCC e ⟧ (toNaryConfig c₂)

-- helper function for choices
CC₂→CC-left-toNaryConfig-choice-case-analyses : ∀ {i : Size} {A : Set} {D : Dimension} {l : CC₂ i A} {r : CC₂ i A}
  → ∀ (c₂ : Configuration₂)
    ---------------------------------------------------------------------------------
  →   ⟦ (if c₂ D then l else r) ⟧₂ c₂
    ≡ ⟦ (choice-elimination (toNaryConfig c₂ D) (toCC l ∷ toCC r ∷ [])) ⟧ (toNaryConfig c₂)
CC₂→CC-left-toNaryConfig-choice-case-analyses {i} {A} {D} {l} {r} c₂ with c₂ D
...                          | true  = ⟦ if true then l else r ⟧₂ c₂                                       ≡⟨⟩
                                       ⟦ l ⟧₂ c₂                                                           ≡⟨ CC₂→CC-left-toNaryConfig l c₂ ⟩
                                       ⟦ toCC l ⟧ (toNaryConfig c₂)                                        ≡⟨⟩
                                       ⟦ (choice-elimination 0 (toCC l ∷ toCC r ∷ [])) ⟧ (toNaryConfig c₂) ∎
                             -- This proof is analoguous to the proof for the "true" case.
                             -- Thus, we simplify the step-by-step-proof to the only reasoning necessary.
...                          | false = CC₂→CC-left-toNaryConfig r c₂

open import Data.List.Properties renaming (map-∘ to mapl-∘)

-- Curiously, the proof is easier for choices than for artifacts.
-- For some reason it was really hard to just prove the application of the induction hypothesis over all subtrees for Artifacts.
-- The use of flip and map made it hard.
-- If we have just artifacts, there is nothing left to do.
CC₂→CC-left-toNaryConfig (Artifact₂ a []) c₂ = refl
-- The semantics "just" recurses on Artifacts.
CC₂→CC-left-toNaryConfig (Artifact₂ a es@(_ ∷ _)) c₂ =
  ⟦ Artifact₂ a es ⟧₂ c₂                                        ≡⟨⟩
  Artifactᵥ a (mapl (λ x → ⟦ x ⟧₂ c₂) es)                        ≡⟨ Eq.cong (λ m → Artifactᵥ a (m es)) -- apply the induction hypothesis below the Artifactᵥ constructor
                                                                   ( mapl-cong-≗-≡ -- and below the mapl
                                                                     (λ {v → CC₂→CC-left-toNaryConfig v c₂})
                                                                   )
                                                                  ⟩
  Artifactᵥ a (mapl (flip (⟦_⟧ ∘ toCC) (toNaryConfig c₂)) es)    ≡⟨ Eq.cong (λ m → Artifactᵥ a m) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ (toNaryConfig c₂)) (mapl toCC es)) ≡⟨⟩
  (⟦ toCC (Artifact₂ a es) ⟧ (toNaryConfig c₂))                  ∎
-- The proof for choices could be greatly simplified because when doing a case analyses on (c₂ D), only the induction hypthesis
-- is necessary for reasoning. We leave the long proof version though because it better explains the proof.
CC₂→CC-left-toNaryConfig (D ⟨ l , r ⟩₂) c₂ =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ c₂                                                                   ≡⟨⟩
  ⟦ if c₂ D then l else r ⟧₂ c₂                                                         ≡⟨ CC₂→CC-left-toNaryConfig-choice-case-analyses c₂ ⟩
  ⟦ choice-elimination ((toNaryConfig c₂) D) (toCC l ∷ toCC r ∷ []) ⟧ (toNaryConfig c₂) ≡⟨⟩
  ⟦ D ⟨ toCC l ∷ toCC r ∷ [] ⟩ ⟧ (toNaryConfig c₂)                                       ≡⟨⟩
  ⟦ toCC (D ⟨ l , r ⟩₂) ⟧ (toNaryConfig c₂)                                              ∎

-- Finally, prove left side by showing that asCC-Conf c₂ is a configuration satisfying the subset relation. (We substitute asCC-Conf c₂ for the configuration in ∃ [c] ... in the relation).
CC₂→CC-left {i} {A} {e} c₂ = toNaryConfig c₂ , CC₂→CC-left-toNaryConfig e c₂
```

#### Proof of the right side

This proof is very similar to the left side. Maybe we can simplify both proofs if we extract some similarities.
```agda
CC₂→CC-right-toBinaryConfig : ∀ {i : Size} {A : Set}
  → ∀ (e : CC₂ i A)
  → ∀ (c : Configuration)
    ------------------------------------
  → ⟦ e ⟧₂ (toBinaryConfig c) ≡ ⟦ toCC e ⟧ c

-- case analyses for choices where we either have to proceed the proof on the left or right side of a binary choice depending on our configuration
CC₂→CC-right-toBinaryConfig-choice-case-analysis : ∀ {i : Size} {A : Set} {D : Dimension} {l r : CC₂ i A}
  → ∀ (c : Configuration)
    -------------------------------------------
  →   ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)
    ≡ ⟦ choice-elimination (c D) (toCC l ∷ toCC r ∷ []) ⟧ c
CC₂→CC-right-toBinaryConfig-choice-case-analysis {i} {A} {D} {l} {r} c with c D
... | zero  = CC₂→CC-right-toBinaryConfig l c
... | suc n = CC₂→CC-right-toBinaryConfig r c

CC₂→CC-right-toBinaryConfig (Artifact₂ a []) c = refl
CC₂→CC-right-toBinaryConfig (Artifact₂ a es@(_ ∷ _)) c =
  ⟦ Artifact₂ a es ⟧₂ (toBinaryConfig c)               ≡⟨⟩
  Artifactᵥ a (mapl (flip ⟦_⟧₂ (toBinaryConfig c)) es) ≡⟨ Eq.cong (λ {m → Artifactᵥ a (m es)}) (mapl-cong-≗-≡ (λ {v → CC₂→CC-right-toBinaryConfig v c})) ⟩
  Artifactᵥ a (mapl ((flip ⟦_⟧ c) ∘ toCC) es)           ≡⟨ Eq.cong (λ {x → Artifactᵥ a x}) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ c) (mapl toCC es))       ≡⟨⟩
  ⟦ toCC (Artifact₂ a es) ⟧ c                          ∎
CC₂→CC-right-toBinaryConfig (D ⟨ l , r ⟩₂) c =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ (toBinaryConfig c)                   ≡⟨⟩
  ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c) ≡⟨ CC₂→CC-right-toBinaryConfig-choice-case-analysis c ⟩
  ⟦ choice-elimination (c D) (toCC l ∷ toCC r ∷ []) ⟧ c ≡⟨⟩
  ⟦ D ⟨ toCC l ∷ toCC r ∷ [] ⟩ ⟧ c                       ≡⟨⟩
  ⟦ toCC (D ⟨ l , r ⟩₂) ⟧ c                              ∎

CC₂→CC-right {i} {A} {e} c = toBinaryConfig c , CC₂→CC-right-toBinaryConfig e c
```

### N-ary to Binary Choice Calculus

To convert choice calculus to binary normal form, we have to convert n-ary choices to binary choices.
We can do so by recursively nesting alternatives beyond the second in nested binary decisions.
This translation follows the similar observations for if-statements that an `elseif` expression is equivalent to an `else` branch with a nested `if`:

      if x
      then a
      elif b
      else c

    ≡ if x
      then a
      else (if x'
            then b
            else c)

One of the key challenges for this translations is to introduce correct new conditions `x'` (i.e., dimensions) for the nested choices.
Here, this means, we have to generate new choices, and thus new dimensions (just as `x'`).
When generating a new name for a new dimension, we have to assume that it does not exist yet or otherwise, we cannot preserve semantics.
For example, when generating names by appending tick marks, we may get `toCC₂ (D⟨a,b,D'⟨c, d⟩⟩) ≡ D⟨a, D'⟨b, D'⟨c, d⟩⟩⟩` which has different semantics than the input.

We identified two possible ways to ensure that new generated names do not collide with existing dimension names:

1. Bake uniqueness into the type-level by using a different type for dimension in the output expression: Values of the new type would ensure that these values were never part of the original input expression. However, this is very intrusive into the language design and introduces complexity for all matters other than conversion to binary normal form. It also obfuscates the language design for an easier solution to this particular problem. That is why we choose the second alternative below.
2. Ensure that any new dimension name does not collide (as shown in the example above). Collision can either occur with names from the input formula or in the output formula. When generating a new name, we can only guarantee that it does not collide with another name in the input formula by comparing it to every name in the input formula. This is an intricate process, vastly complicating proofs. Another strategy would be to ensure that any generated name in the output formula collides exactly with those names in the output formula for which both respective dimensions in the input formula collided. For example, when transforming `D⟨D⟨x, y, z⟩, A⟨u, v, w⟩, n⟩`, we have to introduce new dimensions for `D` and `A` because these have arity greater 2. For both occurences of `D`, the generated dimension has to have the same name to ensure choice synchronization (see Erics PhD thesis). And these two names must collide in the output but must not collide with any other name. For example, `D⟨D⟨x, D'⟨y, z⟩⟩, D'⟨A⟨u, A'⟨v, w⟩⟩, n⟩⟩` would be valid but the generated name `D'` can still collide with names for the input formula.

To prevent collisions of names, we (1) rename every dimension in the input in a consistent way and (2) also generate new names following this way. This allows us to ensure that generated names do not collide with other existing names.
The idea is to append an index to every dimension that indicates the tag that had to be chosen in the input formula to pick that choice's left alternative.

Example: `D⟨x, y, z, w⟩ ↦ D.0⟨x, D.1⟨y, D.2⟨z, w⟩⟩⟩`

Definition:
```agda
open import Data.Nat.Show renaming (show to show-nat)

indexedDim : Dimension → ℕ → Dimension
indexedDim D n = D ++ "." ++ (show-nat n) -- Do not simplify for n ≡ᵇ zero! I know names like A.0 are ugly if we can avoid them but dropping the .0 where possible can cause name collisions in the output formula!
```

Here is an informal proof that using `indexedDim` to rename every dimension does not cause unintended choice synchronizations:

    Every dimension D in the input formula is renamed to (D ++ ".0").
    Thus every dimension is manipulated equally and thus, this transformation is a true renaming.

    Removal of dimensions occurs only for unary choices and cannot invalidate uniqueness of names anyway.

    New dimensions are introduced only to unroll a dimension from the input formula.
    This means, each generated dimension G is associated to exactly one dimension D from the input formula.
    The name of G is (D ++ "." ++ suc n) for an n : ℕ.
    The name of G is new because of proof by contradiction:
      Assume the name of G is not new (i.e., collides).
      This means there is dimension A in the output formula with the same name as G
      but A was associated to another dimension in the input formula.
      The name of A is of the form (I ++ "." m) for an m : ℕ and a dimension I from the input formula.
      Because A has the same name as G, we know that I = D and suc n = m.
      Thus, both A and G originate from the same dimension in the input formula.
      This contradicts our assumption that G collided.

To prove that a translation from choice calculus to binary normal form is semantics-preserving, we have to show that both, the input as well as the output expression, describe the same set of variants (just as we did earlier for the inverse translation).
As we will see later, this requires is to not only translate an expression from n-ary to binary form, but also configurations.
Our implementation of the translation thus takes an n-ary choice calculus expression as input and yields two results: (1) a converter that can translate configurations for the input formula to configurations for the output formula and vice versa, and (2) the expression in binary normal form.
To define the configuration converter, we use the state monad that keeps track of our current progress of translating configurations.

We thus first import the necessary definitions from the standard library:
```agda
-- Import general functor and monad operations.
open import Effect.Functor using (RawFunctor)
--open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

-- Import state monad
open import Effect.Monad.State
  using (State; RawMonadState; runState)
  renaming (functor to state-functor;
            applicative to state-applicative;
            monad to state-monad;
            monadState to state-monad-specifics)

-- Import traversable for lists
import Data.List.Effectful
open Data.List.Effectful.TraversableA using (sequenceA) renaming (mapA to traverse)
```

To convert configurations for the input formula to configurations for the output formula and vice versa, we introduce the following record.
We use this record as the state during our translation.
```agda
-- resembles a specialized version of _⇔_ in the plfa book
record ConfigurationConverter : Set where
  field
    nary→binary : Configuration → Configuration₂
    binary→nary : Configuration₂ → Configuration
open ConfigurationConverter

-- Default configuration converter that always goes left.
-- We use it as a base case when we have no further information.
unknownConfigurationConverter : ConfigurationConverter
unknownConfigurationConverter = record
  { nary→binary = λ _ _ → true
  ; binary→nary = λ _ _ → 0
  }

-- The state we are going to use during the translation from n-ary to binary choice calculus.
-- We keep track of the current configuration converter and update it when necessary.
TranslationState : Set → Set
TranslationState = State ConfigurationConverter
```

We can now define our translation function `toCC₂`.
Sadly, we cannot prove it terminating yet.
The problem is that the alternatives of a choice are a list, and this list is converted to a recursive nesting structure.
For example, D ⟨ a , b , c , d ⟩ becomes D.0 ⟨ a , D.1 ⟨ b , D.2 ⟨ c , d ⟩₂ ⟩₂ ⟩₂.
Hence, the number of children of a CC expression determines the nesting depth of the resulting binary expression.
Since we have no guarantees on the number of children (i.e., no bound / estimate), we cannot make any guarantees on the maximum depth of the resulting expression.
Moreover, because a children list thus could be infinite, also the resulting expression could be infinite.
Thus, this function might indeed not terminate.
To solve this, we would have to introduce yet another bound to n-ary choice calculus: an upper bound for the number of children of each node.
We should later decide if this extra boilerplate is worth it or not.

```agda
-- helper function to keep track of state
{-# TERMINATING #-}
toCC₂' : ∀ {i : Size} {A : Set} → CC i A → TranslationState (CC₂ ∞ A)

-- actural translation function
toCC₂ : ∀ {i : Size} {A : Set} → CC i A → ConfigurationConverter × CC₂ ∞ A
toCC₂ cc = runState (toCC₂' cc) unknownConfigurationConverter

{- |
Unroll choices by recursively nesting any alternatives beyond the first.
Example: D ⟨ u ∷ v ∷ w ∷ [] ⟩ → D.0 ⟨ u, D.1 ⟨ v , w ⟩₂ ⟩₂
-}
toCC₂'-choice-unroll : ∀ {i : Size} {A : Set}
  → Dimension      -- initial dimension in input formula that we translate (D in the example above).
  → ℕ             -- Current alternative of the given dimension we are translating. zero is left-most alternative (pointing to u in the example above).
  → List⁺ (CC i A) -- remaining alternatives of the choice to unroll. We let this shrink recursively.
  → TranslationState (CC₂ ∞ A)

-- Leave artifact structures unchanged but recursively translate all children.
-- Translating all children yields a list of states which we evaluate in sequence.
toCC₂' (Artifact a es) =
  let open RawFunctor state-functor in
  Artifact₂ a <$> (traverse state-applicative toCC₂' es)
toCC₂' (D ⟨ es ⟩) = toCC₂'-choice-unroll D zero es

open import Data.Nat renaming (_≡ᵇ_ to _nat-≡ᵇ_)
open import Util.Util using (empty?)

update-configuration-converter :
    ConfigurationConverter
  → Dimension  -- corresponding dimension in the input n-ary expression
  → ℕ         -- current nesting depth (see toCC₂'-choice-unroll)
  → Dimension  -- name of the corresponding dimension in the output binary expression
  → Bool       -- True iff the currently inspected choice is binary.
  → ConfigurationConverter
update-configuration-converter conf-converter D n D' binary? =
    let n→b = nary→binary conf-converter
        b→n = binary→nary conf-converter
    in record
      -- Given an n-ary configuration cₙ for the input formula, we want to find the value of a given dimension in the binary output formula
      { nary→binary = (λ {cₙ queried-output-dimension →
          -- If the queried dimension was translated from our currently translated dimension D.
          if (queried-output-dimension dim-== D')
          -- If the selection made in the input formula did select the left alternative of our choice
          -- then also pick it in the binary output formula. Otherwise, do not pick it.
          -- In case cₙ D <ᵇ n, the result does not matter. Then, an alternative above this choice was already chosen
          -- (and we are within an else branch). So it does not matter what we pick here. Could be true, false, or n→b cₙ queried-output-dimension.
          -- In case cₙ D >ᵇ n, the result has to be false because the alternative that has to be picked is on the right, which is only checked if we do not go left here.
          then (cₙ D nat-≡ᵇ n)
          -- If not, ask our existing configuration translation knowledge.
          else (n→b cₙ queried-output-dimension)
          })
      -- Given a binary configuration c₂ for the output formula, we want to find the value of a queried dimension in the n-ary input formula.
      ; binary→nary = (λ {c₂ queried-input-dimension →
          let recursive-result = b→n c₂ queried-input-dimension in
          -- If the queried dimension is the dimension we currently translate.
          if (queried-input-dimension dim-== D)
          then (if (c₂ D')       -- If the binary configuration has chosen the left alternative of the nested binary dimension
                then n           -- ... then that is the alternative we have to pick in the input formula.
                else (if binary? -- ... if not, we check if the current choice is already.
                      then suc n -- If it is, we pick the right alternative.
                      else recursive-result -- Otherwise, we check further nested branches recursively.
                      )
                )
          else recursive-result
          })
      }

-- Use the idempotency rule D⟨e⟩≈e to unwrap unary choices.
-- This is where recursion stops.
toCC₂'-choice-unroll D n (e₁ ∷ []) = toCC₂' e₁
-- For n-ary choices with n > 1, convert the head and recursively convert the tail.
toCC₂'-choice-unroll D n (e₁ ∷ e₂ ∷ es) =
  let open RawMonad state-monad
      open RawMonadState state-monad-specifics
  in do
    let D' = indexedDim D n

    -- translation of the formula
    cc₂-e₁   ← toCC₂' e₁
    cc₂-tail ← toCC₂'-choice-unroll D (suc n) (e₂ ∷ es)

    -- translation of configurations
    -- The tail length check is actually a recursion end that checks if we are left with a binary choice.
    -- So we might want to introduce a pattern matching case for binary choices instead of doing this runtime-check here.
    -- However, this abstraction causes more boilerplate than it simplifies.
    -- Let's see how much more complicated the proofs become.
    conf-converter ← get
    put (update-configuration-converter conf-converter D n D' (empty? es))

    pure (D' ⟨ cc₂-e₁ , cc₂-tail ⟩₂)
```

Now we prove that conversion to binary normal form is semantics preserving (i.e., the set of described variants is the same).
```
CC→CC₂-left : ∀ {i : Size} {A : Set} {e : CC i A}
    -------------
  → proj₂ (toCC₂ e) ₂⊂̌ₙ e

CC→CC₂-right : ∀ {i : Size} {A : Set} {e : CC i A}
    -------------
  → e ₙ⊂̌₂ proj₂ (toCC₂ e)

CC→CC₂ : ∀ {i : Size} {A : Set} {e : CC i A}
    ----------
  → proj₂ (toCC₂ e) ₂≚ₙ e
CC→CC₂ {i} {A} {e} =
    CC→CC₂-left  {i} {A} {e}
  , CC→CC₂-right {i} {A} {e}
```

#### Proof of the left side

```agda
-- Every variant described by the translated expression is also described by the initial expression.
CC→CC₂-left' : ∀ {i : Size} {A : Set}
  → ∀ (e : CC i A)
  → ∀ (c₂ : Configuration₂)
    ------------------------------------------------------------------
  → ⟦ proj₂ (toCC₂ e) ⟧₂ c₂ ≡ ⟦ e ⟧ (binary→nary (proj₁ (toCC₂ e)) c₂)

CC→CC₂-left' (Artifact a []) c₂ = refl
CC→CC₂-left' e@(Artifact a es@(_ ∷ _)) c₂ =
  let open RawFunctor state-functor
      c = binary→nary (proj₁ (toCC₂ e)) c₂
  in
  begin
    ⟦ proj₂ (toCC₂ e) ⟧₂ c₂
  ≡⟨⟩
    ⟦ proj₂ (runState (Artifact₂ a <$> (traverse state-applicative toCC₂' es)) unknownConfigurationConverter) ⟧₂ c₂
  ≡⟨⟩
    Artifactᵥ a (mapl (flip ⟦_⟧₂ c₂) (proj₂ (runState (sequenceA state-applicative (mapl toCC₂' es)) unknownConfigurationConverter)))
  -- TODO: Somehow apply the induction hypothesis below the sequenceA below the runState below the mapl below the Artifactᵥ
  ≡⟨ Eq.cong (λ m → Artifactᵥ a m) {!!} ⟩
    Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
  ≡⟨⟩
    ⟦ e ⟧ c
  ∎
CC→CC₂-left' (D ⟨ e ∷ [] ⟩) c₂ =
  let conf = binary→nary (proj₁ (toCC₂ (D ⟨ e ∷ [] ⟩))) c₂ in
  ⟦ proj₂ (toCC₂ (D ⟨ e ∷ [] ⟩)) ⟧₂ c₂ ≡⟨⟩
  ⟦ proj₂ (toCC₂ e            ) ⟧₂ c₂ ≡⟨ CC→CC₂-left' e c₂ ⟩
  ⟦ e           ⟧ conf                ≡⟨⟩
  ⟦ D ⟨ e ∷ [] ⟩ ⟧ conf                ∎
CC→CC₂-left' e@(D ⟨ es@(_ ∷ _ ∷ _) ⟩) c₂ =
  let conf = binary→nary (proj₁ (toCC₂ e)) c₂
      e₂ = proj₂ (toCC₂ e)
  in
  begin
    ⟦ proj₂ (toCC₂ e) ⟧₂ c₂
  --≡⟨ {!!} ⟩
  --  ⟦ if (c₂ D) then {!!} else {!!} ⟧₂ c₂
  ≡⟨ {!!} ⟩
    ⟦ choice-elimination (conf D) es ⟧ conf
  ≡⟨⟩
    ⟦ e ⟧ conf
  ∎

CC→CC₂-left {i} {A} {e} c₂ =
  let conf-trans , cc₂ = toCC₂ e in
  binary→nary conf-trans c₂ , CC→CC₂-left' e c₂
```

#### Proof of the right side

```agda
-- Every variant described by an n-ary CC expression, is also described by its translation to binray CC.
CC→CC₂-right' : ∀ {i : Size} {A : Set}
  → ∀ (e : CC i A)
  → ∀ (c : Configuration)
    -----------------------------------------------------------------
  → ⟦ proj₂ (toCC₂ e) ⟧₂ (nary→binary (proj₁ (toCC₂ e)) c) ≡  ⟦ e ⟧ c

CC→CC₂-right' (Artifact a []) c = refl
CC→CC₂-right' (Artifact a es@(_ ∷ _)) c = {!!}
CC→CC₂-right' (D ⟨ e ∷ [] ⟩) c = CC→CC₂-right' e c -- just apply the induction hypothesis on the only mandatory alternative
CC→CC₂-right' (D ⟨ es@(_ ∷ _ ∷ _) ⟩) c = {!!}

CC→CC₂-right {i} {A} {e} c =
  let conf-trans , cc₂ = toCC₂ e in
  nary→binary conf-trans c , CC→CC₂-right' e c
```

## Example and Test Time

### Examples

```agda
CCExample : Set
CCExample = String × CC ∞ String -- name and expression

-- some smart constructors
chcA : ∀ {i : Size} {A : Set} → List⁺ (CC i A) → CC (↑ i) A
chcA es = "A" ⟨ es ⟩

chcA-leaves : ∀ {i : Size} {A : Set} → List⁺ A → CC (↑ ↑ i) A
chcA-leaves es = chcA (leaves es)

-- examples

ccex-ekko : CCExample
ccex-ekko = "ekko" , cc_example_walk

ccex-binary : CCExample
ccex-binary = "binary" , "D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩

ccex-binary-nested : CCExample
ccex-binary-nested = "binary-nested" ,
  "A" ⟨ ("A" ⟨ leaf "1" ∷ leaf "2" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "3" ∷ leaf "4" ∷ [] ⟩) ∷ []
      ⟩

ccex-ternary-nested : CCExample
ccex-ternary-nested = "ternary-nested" ,
  chcA ( chcA-leaves ("1" ∷ "2" ∷ "3" ∷ []) ∷
         chcA-leaves ("4" ∷ "5" ∷ "6" ∷ []) ∷
         chcA-leaves ("7" ∷ "8" ∷ "9" ∷ []) ∷ [])

ccex-complex1 : CCExample
ccex-complex1 = "complex1" ,
  "A" ⟨ ("B" ⟨ leaf "1" ∷ leaf "2" ∷ leaf "3" ∷ [] ⟩) ∷
        ("C" ⟨ leaf "c" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "4" ∷
               ("D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩) ∷
               leaf "5" ∷ []
             ⟩) ∷ []
      ⟩

ccex-nametrick : CCExample
ccex-nametrick = "name-trick" ,
  "A" ⟨ ("A.0" ⟨ leaf "A.0-left" ∷ leaf "A.0-right" ∷ [] ⟩) ∷ leaf "x" ∷ [] ⟩

ccex-all : List CCExample
ccex-all =
  ccex-ekko ∷
  ccex-binary ∷
  ccex-binary-nested ∷
  ccex-ternary-nested ∷
  ccex-complex1 ∷
  ccex-nametrick ∷
  []
```

### Print Helper Functions

Extra imports/opening of functions we use for conversion to string of some data structures:
```agda
open Data.String using (unlines; intersperse)
open Data.List using (concatMap) renaming (_++_ to _++l_)
open Function using (id)

open import Util.ShowHelpers
```

Showing choice calculus expressions:
```agda
showCC : ∀ {i : Size} → CC i String → String
showCC (Artifact a []) = a
showCC (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl showCC es)) ++ ">-"
showCC (D ⟨ es ⟩) = D ++ "<" ++ (Data.String.intersperse ", " (toList (mapl⁺ showCC es))) ++ ">"

showCC₂ : ∀ {i : Size} → CC₂ i String → String
showCC₂ (Artifact₂ a []) = a
showCC₂ (Artifact₂ a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl showCC₂ es)) ++ ">-"
showCC₂ (D ⟨ l , r ⟩₂) = D ++ "<" ++ (showCC₂ l) ++ ", " ++ (showCC₂ r) ++ ">"

open SemanticDomains using (showVariant)
```

Helper functions to collect all dimensions within a choice calculus expression. These might give duplicates because we use lists instead of sets for implementation convenience:
```agda
-- get all dimensions used in a CC expression
dims-CC : ∀ {i : Size} {A : Set} → CC i A → List Dimension
dims-CC (Artifact _ es) = concatMap dims-CC es
dims-CC (D ⟨ es ⟩) = D ∷ concatMap dims-CC (toList es)

-- get all dimensions used in a binary CC expression
dims-CC₂ : ∀ {i : Size} {A : Set} → CC₂ i A → List Dimension
dims-CC₂ (Artifact₂ _ es) = concatMap dims-CC₂ es
dims-CC₂ (D ⟨ l , r ⟩₂) = D ∷ (dims-CC₂ l ++l dims-CC₂ r)
```

Print all values of a configuration for a list of given dimensions:
```agda
show-nary-config : Configuration → List Dimension → String
show-nary-config = show-fun {Dimension} {ℕ} id show-nat

show-binary-config : Configuration₂ → List Dimension → String
show-binary-config = show-fun {Dimension} {Bool} id show-bool
```

Make a configuration that always selects n and also generate its name.
```agda
selectₙ : ℕ → Configuration × String
selectₙ n = (λ {_ → n}) , ("(λ d → " ++ (show-nat n) ++ ")")
```

### Conversion of Examples to Binary CC and Back
Convert a given named choice calculus formula to binary normal form and back and print all intermediate results.
Do so for two configurations, one configuration that always selects 0, and one that always selects 1.
```agda
ccex-toBinaryAndBack : CCExample → String
ccex-toBinaryAndBack (name , cc) = unlines (
  let
    configconverter , cc₂ = toCC₂ cc
    n→b = nary→binary configconverter
    b→n = binary→nary configconverter

    evalₙ : Configuration × String → String
    evalₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ cname ++ " = "
      ++ (showVariant (⟦ cc ⟧ conf))}

    eval₂ : Configuration × String → String
    eval₂ = λ { (conf , cname) →
      "[[toCC₂ " ++ name ++ "]] " ++ "(n→b " ++ cname ++ ")" ++ " = "
      ++ (showVariant (⟦ cc₂ ⟧₂ (n→b conf)))}

    eval₂ₙ : Configuration × String → String
    eval₂ₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ "(b→n (n→b " ++ cname ++ "))" ++ " = "
      ++ (showVariant (⟦ cc ⟧ (b→n (n→b conf))))}

    eval-selectₙ = evalₙ ∘ selectₙ
    eval-select₂ = eval₂ ∘ selectₙ
    eval-select₂ₙ = eval₂ₙ ∘ selectₙ

    show-config-named : (Configuration × String → String × String) → ℕ → String
    show-config-named = λ show-config n →
      let conf-print , name = show-config (selectₙ n)
      in
      name ++ ": " ++ conf-print
    show-selectₙ = show-config-named (λ (conf , name) → show-nary-config conf (dims-CC cc) , name)
    show-select₂ = show-config-named (λ (conf , name) → (show-binary-config ∘ n→b) conf (dims-CC₂ cc₂) , ("n→b " ++ name))
    show-select₂ₙ = show-config-named (λ (conf , name) → (show-nary-config ∘ b→n ∘ n→b) conf (dims-CC cc) , ("b→n (n→b " ++ name ++ ")"))
  in
  ("=== Example: " ++ name ++ " ===") ∷
  (name ++ " = " ++ (showCC cc)) ∷
  (show-selectₙ 0) ∷
  (show-selectₙ 1) ∷
  (show-selectₙ 2) ∷
  (eval-selectₙ 0) ∷
  (eval-selectₙ 1) ∷
  (eval-selectₙ 2) ∷
  ("toCC₂ " ++ name ++ " = " ++ (showCC₂ cc₂)) ∷
  (show-select₂ 0) ∷
  (show-select₂ 1) ∷
  (show-select₂ 2) ∷
  (eval-select₂ 0) ∷
  (eval-select₂ 1) ∷
  (eval-select₂ 2) ∷
  (name ++ " with configurations converted back and forth ") ∷
  (show-select₂ₙ 0) ∷
  (show-select₂ₙ 1) ∷
  (show-select₂ₙ 2) ∷
  (eval-select₂ₙ 0) ∷
  (eval-select₂ₙ 1) ∷
  (eval-select₂ₙ 2) ∷
  [])
```

### Final Printing
Print the binary-conversion for all examples:
```agda
mainStr : String
mainStr = intersperse "\n\n" (mapl ccex-toBinaryAndBack ccex-all)
```

## Unicode Characters in Emacs Agda Mode

See [Unicode.md](../Unicode.md).

