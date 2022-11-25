# Choice Calculus in Agda

## Options

For termination checking, we have to use sized types (i.e., types that are bounded by a certain size).
We use sizes to constrain the maximum tree-depth of an expression.
```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module CC where
```

## Imports
```agda
-- Imports from Standard Library
open import Data.List.Base
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty.Base
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat.Base
  using (ℕ; zero; suc; NonZero)
open import Data.String.Base
  using (String; _++_)
open import Function.Base
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

-- When just speaking of core choice calculus, we neither care for nor know the depth of an expression. So infinity is a proper upper bound here as we just speak about expressions of arbitrary depth.
CoreCC : Set → Set
CoreCC = CC ∞

-- Increasing the upper bound is always valid.
-- For example, an expression which has at most depth d, also is at most d+1 deep.
weakenDepthBound : ∀ {i : Size} {j : Size< i} {A : Set} → CC j A → CC i A
weakenDepthBound c = c
```

Choice calculus has denotational semantics, introduced by Eric in the TOSEM paper and his PhD thesis.
Semantics for choice calculus can be defined in different ways.
In his phd thesis, Eric defined the semantics to be the set of all variants described by the expression.
So the semantic domain was a set of choice calculus expressions without any choices.
We can encode a choice calculus expression without choices at the type level:
```agda
data Variant (A : Set) : Set where
  Artifactᵥ : A → List (Variant A) → Variant A
```
This is basically just a tree structure of artifacts.

An equivalent definition produces a configuration function `Config → Variant` that generates variants from configurations.
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

-- Semantic equivalence ≈ inherits all properties from structural equality ≡ because it is just an alias.

-- Structural equality implies semantic equality.
≡→≈ : ∀ {i : Size} {A : Set} {a b : CC i A}
  → a ≡ b
    -------
  → a ≈ b
≡→≈ eq rewrite eq = refl
```

Some transformation rules
```agda
D⟨e⟩≈e : ∀ {i : Size} {A : Set} {e : CC i A} {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≈ e
D⟨e⟩≈e = refl
```

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence.
Each variant that can be derived from the first CC expression, can also be derived from the second CC expression and vice versa.
We thus first describe the variant-subset relation ⊂̌ and then define variant-equality as a bi-directional subset. 
```agda
{-
For the variant-subset relation, we want to express the following, given two expressions e₁ e₂:

Every variant described by e₁
is also described by e₂.

->

∀ variants v in the image of ⟦ e₁ ⟧
there exists a configuration c
such that ⟦ e₂ ⟧ c ≡ v.

->

For all configurations c₁
there exists a configuration c₂
such that ⟦ e₁ ⟧ c₁ = ⟦ e₂ ⟧ c₂.
-}
open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.Product using (_×_; proj₁; proj₂)

-- Beware! This symbol renders different on Github. The v should be on top of ⊂ but on Github is next to it.
-- So don't be confused in case the v appears on top of a character next to ⊂.
-- Unicode for ⊂̌ is \sub\v
_⊂̌_ : ∀ {i j : Size} {A : Set}
  → (e₁ : CC i A) → (e₂ : CC j A) → Set
e₁ ⊂̌ e₂ = ∀ (c₁ : Configuration) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
infix 5 _⊂̌_

-- some properties
-- _⊂̌_ is not symmetric

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
-- For some reason we keep to have reapeating the implicit parameters which is a bit annoying but still ok because the proves are short.
```

Finally, let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
-- smart constructor for plain artifacts
-- Any upper bound is fine but we are at least 1 deep.
leaf : ∀ {i : Size} {A : Set} → A → CC (↑ i) A
leaf a = Artifact a []

cc_example_walk : ∀ {i : Size} → CC (↑ ↑ i) String
cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

-- Any upper bound is fine but we are at least 2 deep.
cc_example_walk_zoom : Variant String
cc_example_walk_zoom = ⟦ cc_example_walk ⟧ (λ {"Ekko" → 0; _ → 0})
```

Print the example:
```agda
-- We omit proving termination for debugging stuff.
-- TODO: Move this function to another file and forbid TERMINATING macro in the CC module.
{-# TERMINATING #-}
showVariant : Variant String → String
showVariant (Artifactᵥ a []) = a
showVariant (Artifactᵥ a es) = a ++ "-<" ++ (Data.List.Base.foldl _++_ "" (mapl showVariant es)) ++ ">-"

mainStr : String
mainStr = showVariant cc_example_walk_zoom
```

## Algebraic Decision Diagrams and Binary Normal Form

In the following we introduce normal forms for choice calculus expressions.
We express each normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.

An algebaric decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ (FFSPL) and the 1997 ADD paper, ADDs are defined to be binary.
```agda
open import Data.Bool using (Bool; true; false; if_then_else_)

-- TODO: Make sized
data ADD (A : Set) : Set where
  Terminal : A → ADD A -- ModelBase in FFSPL
  Choice : Dimension → ADD A → ADD A → ADD A -- ModelChoice in FFSPL (has a presence condition here instead of a dimension)

-- BDDs are ADDs in which we can only end at true or false.
BDD : Set
BDD = ADD Bool
```

To convert to product normal form, it is easier to first convert to binary normal form of choice calculus.
Every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.
```agda
Tag₂ : Set
Tag₂ = Bool

left  = true
right = false

asTag : Tag₂ → Tag
asTag true  = 0
asTag false = 1

asTag₂ : Tag → Tag₂
asTag₂ zero    = true
asTag₂ (suc n) = false

data CC₂ (i : Size) (A : Set) : Set where
  Artifact₂ : {j : Size< i} →
    A → List (CC₂ j A) → CC₂ i A
  _⟨_,_⟩₂ : {j : Size< i} →
    Dimension → CC₂ j A → CC₂ j A → CC₂ i A

-- Semantics for binary choice calculus
Configuration₂ : Set
Configuration₂ = Dimension → Tag₂

⟦_⟧₂ : ∀ {i : Size} {A : Set} → CC₂ i A → Configuration₂ → Variant A
⟦ Artifact₂ a es ⟧₂ c = Artifactᵥ a (mapl (flip ⟦_⟧₂ c) es)
⟦ D ⟨ l , r ⟩₂ ⟧₂ c = ⟦ if (c D) then l else r ⟧₂ c
```

Now that we've introduce the binary normal form at the type level, we want to show that (1) any n-ary choice calculus expression can be transformed to binary normal form, and (2) any binary normal form expression is a choice calculus expression.
We start with the second task: Converting a choice calculus expression of which we know at the type level that it is in binary normal form, back to n-ary choice calculus.
It will still be an expression in binary normal form but we will lose that guarantee at the type level.
```agda
{- |
Convert back to normal choice calculus.
Converts a binary choice calculus expression to a core choice calculus expression.
The resulting expression is syntactically equivalent and thus still in binary normal form.
We drop only the knowledge of being in binary normal form at the type level.
-}
asCC : ∀ {i : Size} {A : Set} → CC₂ i A → CC i A
asCC (Artifact₂ a es) = Artifact a (mapl asCC es)
asCC (D ⟨ l , r ⟩₂) = D ⟨ (asCC l) ∷ (asCC r) ∷ [] ⟩

{- |
Convert binary configuration to n-ary configuration.
-}
toNaryConfig : Configuration₂ → Configuration
toNaryConfig c₂ = asTag ∘ c₂

{- |
Convert n-ary configuration to binary.
-}
toBinaryConfig : Configuration → Configuration₂
toBinaryConfig c = asTag₂ ∘ c
```

To prove that both conversions are valid, we define semantic equivalence between a binary, and an n-ary choice calculus expression.
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

And now for the proofs.
We prove first that any binary choice calculus expression can be converted to an n-ary choice calculus expression (core choice calculus expression).
```agda
CC₂→CC-left : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → e ₂⊂̌ₙ asCC e

CC₂→CC-right : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → asCC e ₙ⊂̌₂ e

-- Main theorem for drawing an arrow from CC₂ to CC.
CC₂→CC : ∀ {i : Size} {A : Set} {e : CC₂ i A}
    ------------
  → e ₂≚ₙ asCC e
CC₂→CC {i} {A} {e} =
    CC₂→CC-left  {i} {A} {e}
  , CC₂→CC-right {i} {A} {e}
```

Proof of the left side:
```agda
-- helper function that tells us that the existing n-ary configuration, given a binary configuration, is toNaryConfig c₂. That basically unwraps the ∃ and avoids to write pairs all the time.
CC₂→CC-left-toNaryConfig : ∀ {i : Size} {A : Set}
  → ∀ (e : CC₂ i A)
  → ∀ (c₂ : Configuration₂)
    -------------------------------------
  → ⟦ e ⟧₂ c₂ ≡ ⟦ asCC e ⟧ (toNaryConfig c₂)

-- helper function for choices
CC₂→CC-left-toNaryConfig-choice-case-analyses : ∀ {i : Size} {A : Set} {D : Dimension} {l : CC₂ i A} {r : CC₂ i A}
  → ∀ (c₂ : Configuration₂)
    ---------------------------------------------------------------------------------
  →   ⟦ (if c₂ D then l else r) ⟧₂ c₂
    ≡ ⟦ (choice-elimination (toNaryConfig c₂ D) (asCC l ∷ asCC r ∷ [])) ⟧ (toNaryConfig c₂)
CC₂→CC-left-toNaryConfig-choice-case-analyses {i} {A} {D} {l} {r} c₂ with c₂ D
...                          | true  = begin
                                         ⟦ if true then l else r ⟧₂ c₂
                                       ≡⟨⟩
                                         ⟦ l ⟧₂ c₂
                                       ≡⟨ CC₂→CC-left-toNaryConfig l c₂ ⟩
                                         ⟦ asCC l ⟧ (toNaryConfig c₂)
                                       ≡⟨⟩
                                         ⟦ (choice-elimination 0 (asCC l ∷ asCC r ∷ [])) ⟧ (toNaryConfig c₂)
                                       ∎
                             -- This proof is analoguous to the proof for the "true" case.
                             -- Thus, we simplify the step-by-step-proof to the only reasoning necessary.
...                          | false = CC₂→CC-left-toNaryConfig r c₂

open import Data.List.Properties renaming (map-compose to mapl-∘)

-- Curiously, the proof is easier for choices than for artifacts.
-- For some reason it was really hard to just prove the application of the induction hypothesis over all subtrees for Artifacts.
-- The use of flip and map made it hard.
-- If we have just artifacts, there is nothing left to do.
CC₂→CC-left-toNaryConfig (Artifact₂ a []) c₂ = refl
-- The semantics "just" recurses on Artifacts.
CC₂→CC-left-toNaryConfig (Artifact₂ a es@(_ ∷ _)) c₂ =
  begin
    (⟦ Artifact₂ a es ⟧₂ c₂)
  ≡⟨⟩
    Artifactᵥ a (mapl (λ x → ⟦ x ⟧₂ c₂) es)
  ≡⟨ Eq.cong (λ m → Artifactᵥ a (m es)) -- apply the induction hypothesis below the Artifactᵥ constructor
     ( mapl-cong-≗-≡ -- and below the mapl
       (λ {v → CC₂→CC-left-toNaryConfig v c₂})
     )
   ⟩
     Artifactᵥ a (mapl (flip (⟦_⟧ ∘ asCC) (toNaryConfig c₂)) es)
  ≡⟨ Eq.cong (λ m → Artifactᵥ a m) (mapl-∘ es) ⟩
    Artifactᵥ a (mapl (flip ⟦_⟧ (toNaryConfig c₂)) (mapl asCC es))
  ≡⟨⟩
    (⟦ asCC (Artifact₂ a es) ⟧ (toNaryConfig c₂))
  ∎
-- The proof for choices could be greatly simplified because when doing a case analyses on (c₂ D), only the induction hypthesis
-- is necessary for reasoning. We leave the long proof version though because it better explains the proof.
CC₂→CC-left-toNaryConfig (D ⟨ l , r ⟩₂) c₂ =
  begin
    ⟦ D ⟨ l , r ⟩₂ ⟧₂ c₂
  ≡⟨⟩
    ⟦ if c₂ D then l else r ⟧₂ c₂
  ≡⟨ CC₂→CC-left-toNaryConfig-choice-case-analyses c₂ ⟩
    ⟦ choice-elimination ((toNaryConfig c₂) D) (asCC l ∷ asCC r ∷ []) ⟧ (toNaryConfig c₂)
  ≡⟨⟩
    ⟦ D ⟨ asCC l ∷ asCC r ∷ [] ⟩ ⟧ (toNaryConfig c₂)
  ≡⟨⟩
    ⟦ asCC (D ⟨ l , r ⟩₂) ⟧ (toNaryConfig c₂)
  ∎

-- Finally, prove left side by showing that asCC-Conf c₂ is a configuration satisfying the subset relation. (We substitute asCC-Conf c₂ for the configuration in ∃ [c] ... in the relation).
CC₂→CC-left {i} {A} {e} c₂ = toNaryConfig c₂ , CC₂→CC-left-toNaryConfig e c₂
```

Proof of the right side. This proof is very similar to the left side. Maybe we can simplify both proofs if we extract some similarities.
```agda
CC₂→CC-right-toBinaryConfig : ∀ {i : Size} {A : Set}
  → ∀ (e : CC₂ i A)
  → ∀ (c : Configuration)
    ------------------------------------
  → ⟦ e ⟧₂ (toBinaryConfig c) ≡ ⟦ asCC e ⟧ c

-- case analyses for choices where we either have to proceed the proof on the left or right side of a binary choice depending on our configuration
CC₂→CC-right-toBinaryConfig-choice-case-analysis : ∀ {i : Size} {A : Set} {D : Dimension} {l r : CC₂ i A}
  → ∀ (c : Configuration)
    -------------------------------------------
  →   ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)
    ≡ ⟦ choice-elimination (c D) (asCC l ∷ asCC r ∷ []) ⟧ c
CC₂→CC-right-toBinaryConfig-choice-case-analysis {i} {A} {D} {l} {r} c with c D
... | zero  = CC₂→CC-right-toBinaryConfig l c
... | suc n = CC₂→CC-right-toBinaryConfig r c

CC₂→CC-right-toBinaryConfig (Artifact₂ a []) c = refl
CC₂→CC-right-toBinaryConfig (Artifact₂ a es@(_ ∷ _)) c =
  begin
    ⟦ Artifact₂ a es ⟧₂ (toBinaryConfig c)
  ≡⟨⟩
    Artifactᵥ a (mapl (flip ⟦_⟧₂ (toBinaryConfig c)) es)
  ≡⟨ Eq.cong (λ {m → Artifactᵥ a (m es)}) (mapl-cong-≗-≡ (λ {v → CC₂→CC-right-toBinaryConfig v c})) ⟩
    Artifactᵥ a (mapl ((flip ⟦_⟧ c) ∘ asCC) es)
  ≡⟨ Eq.cong (λ {x → Artifactᵥ a x}) (mapl-∘ es) ⟩
    Artifactᵥ a (mapl (flip ⟦_⟧ c) (mapl asCC es))
  ≡⟨⟩
    ⟦ asCC (Artifact₂ a es) ⟧ c
  ∎
CC₂→CC-right-toBinaryConfig (D ⟨ l , r ⟩₂) c =
  begin
    ⟦ D ⟨ l , r ⟩₂ ⟧₂ (toBinaryConfig c)
  ≡⟨⟩
    ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)
  ≡⟨ CC₂→CC-right-toBinaryConfig-choice-case-analysis c ⟩
    ⟦ choice-elimination (c D) (asCC l ∷ asCC r ∷ []) ⟧ c
  ≡⟨⟩
    ⟦ D ⟨ asCC l ∷ asCC r ∷ [] ⟩ ⟧ c
  ≡⟨⟩
    ⟦ asCC (D ⟨ l , r ⟩₂) ⟧ c
  ∎

CC₂→CC-right {i} {A} {e} c = toBinaryConfig c , CC₂→CC-right-toBinaryConfig e c
```

To implement transformation to binary normal form, we have to generate new choices, and thus new dimensions.
When generating a new name for a new dimension, we have to assume that it does not exist yet or otherwise, we cannot preserve semantics.
For example, when generating names by appending tick marks, we may get `toCC₂ (D⟨a,b,D'⟨c, d⟩⟩) ≡ D⟨a, D'⟨b, D'⟨c, d⟩⟩⟩` which has different semantics than the input.
```agda
newDim : Dimension → Dimension
newDim s = s ++ "'"

{-
Sadly, we cannot prove this terminating yet.
The problem is that a list of children is converted to a recursive nesting structure.
For example, D ⟨ a , b , c , d ⟩ becomes D ⟨ a , D' ⟨ b , D'' ⟨ c , d ⟩₂ ⟩₂ ⟩₂.
So the number of children of a CC expression determines the nesting depth of the resulting binary expression.
Since we have no guarantees on the number of children (i.e., no bound / estimate), we cannot make any guarantees on the maximum depth of the resulting expression.
Moreover, because a children list thus could be infinite, also the resulting expression could be infinite.
Thus, this function might indeed not terminate.
To solve this, we would have to introduce yet another bound to n-ary choice calculus: an upper bound for the number of children of each node.
-}
{-# TERMINATING #-}
toCC₂ : ∀ {i : Size} {A : Set} → CC i A → CC₂ ∞ A
-- Leave structures unchanged
toCC₂ (Artifact a es) = Artifact₂ a (mapl toCC₂ es)
-- Use the idempotency rule to unwrap unary choices
toCC₂ (D ⟨ e ∷ [] ⟩) = toCC₂ e
-- Leave binary choices unchanged
toCC₂ (D ⟨ then ∷ elze ∷ [] ⟩) = D ⟨ toCC₂ then , toCC₂ elze ⟩₂
-- Perform recursive nesting on choices with arity n > 2.
toCC₂ (D ⟨ e₁ ∷ e₂ ∷ e₃ ∷ es ⟩) = D ⟨ toCC₂ e₁ , toCC₂ (newDim D ⟨ e₂ ∷ e₃ ∷ es ⟩) ⟩₂
```

Now we prove that conversion to binary normal form is semantics preserving (i.e., the set of described variants is the same).
```
{-
--- Todo ---
How to handle naming in toCC₂?
We have to either prove or assume that all new names introduced in that function are unique.
How can we express that without opening the box of pandora?
Maybe redefining Dimension to ℕ or something more convenient than String could help?
It should remain close to the definition in Eric's thesis/papers though.
-}
```

## Unicode Characters in Emacs Agda Mode
```text
≗ is \=o
≈ is \~~
⊂̌ is \sub\v
≚ is \or=

₁ is \_1
₂ is \_2
ₙ is \_n
```

