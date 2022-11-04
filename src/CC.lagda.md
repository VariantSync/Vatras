```agda
module CC where

open import Function.Base

open import Data.String.Base
  using (String; _++_)
open import Data.Nat.Base
  using (ℕ; zero; suc; _*_; NonZero) renaming (_+_ to _+++_)
open import Data.List.Base
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty.Base
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Extensionality using (extensionality)
```

# Choice Calculus in Agda

Let's define core choices calculus as defined in Eric's phd thesis:
```agda
Dimension : Set
Dimension = String

Tag : Set
Tag = ℕ

data CC (A : Set) : Set where
  Artifact : A → List (CC A) → CC A
  _⟨_⟩ : Dimension → List⁺ (CC A) → CC A
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
open import Data.Fin.Base
open import AuxProofs

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

{-# TERMINATING #-}
⟦_⟧ : {A : Set} → CC A → Configuration → Variant A
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ alternatives ⟩ ⟧ c = ⟦ choice-elimination (c D) alternatives ⟧ c
```

Semantic equivalence means that the same configurations yield the same variants:
```agda
_≈_ : {A : Set} (a b : CC A) → Set
a ≈ b = ⟦ a ⟧ ≡ ⟦ b ⟧
infix 5 _≈_

-- Semantic equivalence ≈ inherits all properties from structural equality ≡ because it is just an alias.

-- Structural equality implies semantic equality.
≡→≈ : ∀ {A : Set} (a b : CC A)
  → a ≡ b
    -------
  → a ≈ b
≡→≈ _ _ eq rewrite eq = refl

module _≈_-Reasoning {A : Set} where
  infix  1 ≈-begin_
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_
  infix  3 _≈-∎

  ≈-begin_ : ∀ {a b : CC A}
    → a ≈ b
      -----
    → a ≈ b
  ≈-begin eq = eq

  _≈⟨⟩_ : ∀ (a : CC A) {b : CC A}
    → a ≈ b
      -----
    → a ≈ b
  a ≈⟨⟩ eqchain = eqchain

  _≈⟨_⟩_ : ∀ (a : CC A) {b c : CC A}
    → a ≈ b
    → b ≈ c
      -----
    → a ≈ c
  a ≈⟨ a≈b ⟩ b≈c = Eq.trans a≈b b≈c

  _≈-∎ : ∀ (a : CC A)
      -----
    → a ≈ a
  a ≈-∎ = refl
```

Some transformation rules
```agda
D⟨e⟩≈e : ∀ {A : Set} → {e : CC A} → {D : Dimension}
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

infix 5 _⊂̌_ --\sub\v
_⊂̌_ : ∀ {A : Set} (e₁ e₂ : CC A) → Set
e₁ ⊂̌ e₂ = ∀ (c₁ : Configuration) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)

-- some properties
-- _⊂̌_ is not symmetric

⊂̌-trans : ∀ {A : Set} {e₁ e₂ e₃ : CC A}
  → e₁ ⊂̌ e₂
  → e₂ ⊂̌ e₃
    -------
  → e₁ ⊂̌ e₃
⊂̌-trans x y c₁ =
  -- this somehow resembles the implementation of >>= of state monad
  let (c₂ , eq₁₂) = x c₁
      (c₃ , eq₂₃) = y c₂
  in c₃ , Eq.trans eq₁₂ eq₂₃

-- Variant-preserving equality of CC is structural equality of all described variants.
-- (It is not semantic equality of variants because we do not the semantics of
-- the object language!)
-- unicode for ≚ is \or=.
_≚_ : ∀ {A : Set} (e₁ e₂ : CC A) → Set
e₁ ≚ e₂ = (e₁ ⊂̌ e₂) × (e₂ ⊂̌ e₁)
infix 5 _≚_

-- properties of variant-preserving equivalence
≚-sym : ∀ {A : Set} {e₁ e₂ : CC A}
  → e₁ ≚ e₂
    -------
  → e₂ ≚ e₁
≚-sym (e₁⊂̌e₂ , e₂⊂̌e₁) = e₂⊂̌e₁ , e₁⊂̌e₂

≚-trans : ∀ {A : Set} {e₁ e₂ e₃ : CC A}
  → e₁ ≚ e₂
  → e₂ ≚ e₃
    -------
  → e₁ ≚ e₃
≚-trans {A} {e₁} {e₂} {e₃} (e₁⊂̌e₂ , e₂⊂̌e₁) (e₂⊂̌e₃ , e₃⊂̌e₂) =
    ⊂̌-trans {A} {e₁} {e₂} {e₃} e₁⊂̌e₂ e₂⊂̌e₃
  , ⊂̌-trans {A} {e₃} {e₂} {e₁} e₃⊂̌e₂ e₂⊂̌e₁

-- As an example, we now prove D ⟨ e ∷ [] ⟩ ≚ e.

D⟨e⟩⊂̌e : ∀ {A : Set} → {e : CC A} → {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ⊂̌ e
D⟨e⟩⊂̌e config = ( config , refl )

e⊂̌D⟨e⟩ : ∀ {A : Set} → {e : CC A} → {D : Dimension}
    ---------------
  → e ⊂̌ D ⟨ e ∷ [] ⟩
e⊂̌D⟨e⟩ config = ( config , refl )

D⟨e⟩≚e : ∀ {A : Set} → {e : CC A} → {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e {A} {e} {D} = D⟨e⟩⊂̌e {A} {e} {D} , e⊂̌D⟨e⟩ {A} {e} {D}
```

In fact, we already have proven `D ⟨ e ∷ [] ⟩ ≈ e` earlier, from which `D ⟨ e ∷ [] ⟩ ≚ e` follows:
```agda
-- Semantic equivalence implies variant equivalence.
≈→⊂̌ : ∀ {A : Set} {a b : CC A}
  → a ≈ b
    -----
  → a ⊂̌ b
-- From a≈b, we know that ⟦ a ⟧ ≡ ⟦ b ⟧. To prove subset, we have to show that both sides produce the same variant for a given configuration. We do so by applying the configuration to both sides of the equation of a≈b.
≈→⊂̌ a≈b config = config , Eq.cong (λ ⟦x⟧ → ⟦x⟧ config) a≈b

-- Semantic equivalence implies variant equivalence.
≈→≚ : ∀ {A : Set} {a b : CC A}
  → a ≈ b
    -----
  → a ≚ b
≈→≚ {A} {a} {b} a≈b =
    ≈→⊂̌ {A} {a} {b} a≈b
  , ≈→⊂̌ {A} {b} {a} (Eq.sym a≈b)
```

Finally we get the alternative proof of `D ⟨ e ∷ [] ⟩ ≚ e`:
```agda
D⟨e⟩≚e' : ∀ {A : Set} → {e : CC A} → {D : Dimension}
    ---------------
  → D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e' {A} {e} {D} = ≈→≚ {A} {D ⟨ e ∷ [] ⟩} {e} (D⟨e⟩≈e {A} {e} {D})
-- For some reason we keep to have reapeating the implicit parameters which is a bit annoying but still ok because the proves are short.
```

Finally, let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
-- smart constructor for plain artifacts
leaf : {A : Set} → A → CC A
leaf a = Artifact a []

cc_example_walk : CC String
cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

cc_example_walk_zoom : Variant String
cc_example_walk_zoom = ⟦ cc_example_walk ⟧ (λ {"Ekko" → 0; _ → 0})
```

Print the example:
```agda
{-# TERMINATING #-}
showVariant : Variant String → String
showVariant (Artifactᵥ a []) = a
showVariant (Artifactᵥ a es) = a ++ "-<" ++ (Data.List.Base.foldl _++_ "" (mapl showVariant es)) ++ ">-"

mainStr : String
mainStr = showVariant cc_example_walk_zoom
```

In the following we introduce normal forms for choice calculus expressions.
We express each normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.

An algebaric decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ (FFSPL) and the 1997 ADD paper, ADDs are defined to be binary.
```agda
open import Data.Bool

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

data CC₂ (A : Set) : Set where
  Artifact₂ : A → List (CC₂ A) → CC₂ A
  _⟨_,_⟩₂ : Dimension → CC₂ A → CC₂ A → CC₂ A

-- Semantics for binary choice calculus
Configuration₂ : Set
Configuration₂ = Dimension → Tag₂

{-# TERMINATING #-}
⟦_⟧₂ : {A : Set} → CC₂ A → Configuration₂ → Variant A
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
{-# TERMINATING #-}
asCC : {A : Set} → CC₂ A → CC A
asCC (Artifact₂ a es) = Artifact a (mapl asCC es)
asCC (D ⟨ l , r ⟩₂) = D ⟨ (asCC l) ∷ (asCC r) ∷ [] ⟩

{- |
Convert binary configuration to n-aray configuration.
-}
asCC-Conf : Configuration₂ → Configuration
asCC-Conf conf₂ = asTag ∘ conf₂
```

To prove that both conversions are valid, we define semantic equivalence between a binary, and an n-ary choice calculus expression:
```agda
{- |
Semantic equivalence between a binary and n-ary choice calculus expression.
Both expressions are considered semantically equal if they yield the same variants for all configurations.
-}
_₂≈ₙ_ : ∀ {A : Set} (a : CC₂ A) (b : CC A) → Set
cc₂ ₂≈ₙ ccₙ = ∀ (c₂ : Configuration₂) → ⟦ cc₂ ⟧₂ c₂ ≡ ⟦ ccₙ ⟧ (asCC-Conf c₂)
infix 5 _₂≈ₙ_

-- Proof that converting a choice calculus formula in binary normal form, back to n-ary choice calculus preserves semantics.
asCC-preserves-semantics : ∀ {A : Set} {e : CC₂ A}
    ------------
  → e ₂≈ₙ asCC e

-- helper function to apply the inductive step for artifacts
asCC-preserves-semantics-ind : ∀ {A : Set}
  → (c₂ : Configuration₂)
    ---------------------------------------------
  →   (λ (z : CC₂ A) → ⟦ z ⟧₂ c₂)
    ≡ (λ (z : CC₂ A) → ⟦ asCC z ⟧ (asCC-Conf c₂))
asCC-preserves-semantics-ind {A} c = extensionality (λ x → asCC-preserves-semantics {A} {x} c)

-- helper function for choices
asCC-preserves-semantics-choice-case-analyses : ∀ {A : Set} {D : Dimension} {l r : CC₂ A} (c₂ : Configuration₂)
    ---------------------------------------------------------------------------------
  →   ⟦ (if c₂ D then l else r) ⟧₂ c₂
    ≡ ⟦ (choice-elimination (asCC-Conf c₂ D) (asCC l ∷ asCC r ∷ [])) ⟧ (asCC-Conf c₂)
asCC-preserves-semantics-choice-case-analyses {A} {D} {l} {r} c₂ with c₂ D
...                          | true  = begin
                                         ⟦ if true then l else r ⟧₂ c₂
                                       ≡⟨⟩
                                         ⟦ l ⟧₂ c₂
                                       ≡⟨ asCC-preserves-semantics {A} {l} c₂ ⟩
                                         ⟦ asCC l ⟧ (asCC-Conf c₂)
                                       ≡⟨⟩
                                         ⟦ (choice-elimination 0 (asCC l ∷ asCC r ∷ [])) ⟧ (asCC-Conf c₂)
                                       ∎
                             -- This proof is analoguous to the proof for the "true" case.
                             -- Thus, we simplify the step-by-step-proof to the only reasoning necessary below:
...                          | false = asCC-preserves-semantics {A} {r} c₂

open import Data.List.Properties renaming (map-cong to mapl-cong; map-compose to mapl-∘)
open Extensionality using (≡→≗)

-- proof is a bit intricate because of map and flip
{-# TERMINATING #-}
asCC-preserves-semantics {A} {Artifact₂ a []} c₂ = refl
asCC-preserves-semantics {A} {Artifact₂ a es} c₂ =
  begin
    (⟦ Artifact₂ a es ⟧₂ c₂)
  ≡⟨⟩
    Artifactᵥ a (mapl (λ x → ⟦ x ⟧₂ c₂) es)
  ≡⟨ Eq.cong (λ {m → Artifactᵥ a (m es)}) -- apply the induction hypothesis below the Artifactᵥ constructor
     ( (extensionality ∘ mapl-cong) -- and below the mapl
       (≡→≗ (asCC-preserves-semantics-ind c₂)) -- set the configuration but leave the CC expression x as first parameter
     )
   ⟩
    Artifactᵥ a (mapl (λ x → ⟦ asCC x ⟧ (asCC-Conf c₂)) es)
  ≡⟨ Eq.cong (λ m → Artifactᵥ a m) (mapl-∘ es) ⟩
    Artifactᵥ a (mapl (λ x → ⟦ x ⟧ (asCC-Conf c₂)) (mapl asCC es))
  ≡⟨⟩
    (⟦ asCC (Artifact₂ a es) ⟧ (asCC-Conf c₂))
  ∎
asCC-preserves-semantics {A} {D ⟨ l , r ⟩₂} c₂ =
  begin
    ⟦ D ⟨ l , r ⟩₂ ⟧₂ c₂
  ≡⟨⟩
    ⟦ if c₂ D then l else r ⟧₂ c₂
  ≡⟨ asCC-preserves-semantics-choice-case-analyses c₂ ⟩
    ⟦ choice-elimination ((asCC-Conf c₂) D) (asCC l ∷ asCC r ∷ []) ⟧ (asCC-Conf c₂)
  ≡⟨⟩
    ⟦ D ⟨ asCC l ∷ asCC r ∷ [] ⟩ ⟧ (asCC-Conf c₂)
  ≡⟨⟩
    ⟦ asCC (D ⟨ l , r ⟩₂) ⟧ (asCC-Conf c₂)
  ∎
```

To implement transformation to binary normal form, we have to generate new choices, and thus new names.
When generating a new name, we have to assume that it does not exist yet or otherwise, we cannot preserve semantics.
For example, when generating names by appending tick marks, `toCC₂ (D⟨a,b,D'⟨c, d⟩⟩) = D⟨a, D'⟨b, D'⟨c, d⟩⟩⟩` which has different semantics than the input.
```agda
newDim : Dimension → Dimension
newDim s = s ++ "'"

{-# TERMINATING #-}
toCC₂ : {A : Set} → CC A → CC₂ A
-- Leave structures unchanged
toCC₂ (Artifact a es) = Artifact₂ a (mapl toCC₂ es)
-- Use the idempotency rule to unwrap unary choices
toCC₂ (D ⟨ e ∷ [] ⟩) = toCC₂ e
-- Leave binary choices unchanged
toCC₂ (D ⟨ then ∷ elze ∷ [] ⟩) = D ⟨ toCC₂ then , toCC₂ elze ⟩₂
-- Perform recursive nesting on choices with arity n > 2.
toCC₂ (D ⟨ e₁ ∷ e₂ ∷ es ⟩) = D ⟨ toCC₂ e₁ , toCC₂ ((newDim D) ⟨ e₂ ∷ es ⟩) ⟩₂
```

Now we prove that conversion to binary normal form is semantics preserving (i.e., the set of described variants is the same).
```
-- Todo: Add assumption of different names
CC→CC₂ : ∀ {A : Set}
  → (e : CC A)
    ------------------
  → e ≚ asCC (toCC₂ e)
CC→CC₂ e = {!!}
```
