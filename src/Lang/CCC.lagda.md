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
module Lang.CCC where
```

## Imports
```agda
-- Imports from Standard Library
open import Data.List
  using (List; []; _∷_; lookup; map)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to map⁺)
open import Data.Nat
  using (ℕ; zero; suc; NonZero)
open import Data.Product
  using (_,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Function
  using (flip)
open import Size
  using (Size; ↑_; ∞)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; refl)

-- Imports of own modules
open import Framework.Annotation.Name using (Dimension)
open import Framework.Definitions using (
  𝔸;
  Variant; Artifactᵥ; VMap; forget-last; VariantSetoid;
  𝕃; ℂ; VariabilityLanguage;
  Semantics;
  fromExpression; Artifactˡ;
  forget-variant-size; sequence-forget-size)
open import Relations.Semantic using (_⊢_≣_; _,_⊢_⊆ᵥ_; _,_⊢_≚_; ≣→≚)

open import Util.List using (find-or-last) --lookup-clamped)
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

data CCC : 𝕃 where
  Artifact : Artifactˡ CCC
  _⟨_⟩ : ∀ {i : Size} {A : 𝔸} →
    Dimension → List⁺ (CCC i A) → CCC (↑ i) A
```

Smart constructors for plain artifacts.
Any upper bound is fine but we are at least 1 deep.
```agda
leaf : ∀ {i : Size} {A : 𝔸} → A → CCC (↑ i) A
leaf a = Artifact a []

leaves : ∀ {i : Size} {A : 𝔸} → List⁺ A → List⁺ (CCC (↑ i) A)
leaves = map⁺ leaf

-- upcast : ∀ {i : Size} {j : Size< i} {A : 𝔸} → CCC j A → CCC i A
-- upcast e = e
```

## Semantics

Choice calculus has denotational semantics, introduced by Eric in the TOSEM paper and his PhD thesis.
Semantics for choice calculus can be defined in different ways.
In his phd thesis, Eric defined the semantics to be the set of all variants described by the expression.
So the semantic domain was a set of choice calculus expressions without any choices.
We can encode a choice calculus expression without choices at the type level as Variants.

An equivalent definition of semantics produces a configuration function `Config → Variant` that generates variants from configurations.
This definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags, according to Eric's phd thesis:
```agda
Configuration : ℂ
Configuration = Dimension → Tag
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to introduce complex error handling and we cannot easily define a configuration to only produce tags within ranges.

```agda
-- Selects the alternative at the given tag.
choice-elimination : ∀ {A : 𝔸} → Tag → List⁺ A → A
choice-elimination = find-or-last

{-|
Semantics of core choice calculus.
The semantic domain is a function that generates variants given configurations.
-}
⟦_⟧ : Semantics CCC Configuration
⟦ Artifact a es ⟧ c = Artifactᵥ a (map (flip ⟦_⟧ c) es)
⟦ D ⟨ alternatives ⟩ ⟧ c = ⟦ choice-elimination (c D) alternatives ⟧ c

CCCL : VariabilityLanguage
CCCL = record
  { expression    = CCC
  ; configuration = Configuration
  ; semantics     = ⟦_⟧
  }
```

## Properties

Some transformation rules
```agda
-- unary choices are mandatory
D⟨e⟩≣e : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
    ------------------------
  → CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣ e
D⟨e⟩≣e _ = refl

-- -- other way to prove the above via variant-equivalence

D⟨e⟩⊆e : ∀ {i : Size} {A : 𝔸} {e : CCC i A} {D : Dimension}
    -------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ⊆ᵥ e
D⟨e⟩⊆e c = c , refl

e⊆D⟨e⟩ : ∀ {i : Size} {A : 𝔸} {e : CCC i A} {D : Dimension}
    -------------------------------
  → CCCL , CCCL ⊢ e ⊆ᵥ D ⟨ e ∷ [] ⟩
e⊆D⟨e⟩ c = c , refl

D⟨e⟩≚e : ∀ {i : Size} {A : 𝔸} {e : CCC i A} {D : Dimension}
    ------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e {i} {A} {e} {D} = D⟨e⟩⊆e {i} {A} {e} {D} , e⊆D⟨e⟩ {i} {A} {e} {D}

D⟨e⟩≚e' : ∀ {i : Size} {A : 𝔸} {e : CCC i A} {D : Dimension}
    ------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e' {i} {A} {e} {D} =
  ≣→≚ {A} {CCCL}
      {fromExpression CCCL (D ⟨ e ∷ [] ⟩)} {fromExpression CCCL e}
      (D⟨e⟩≣e {i} {A} {e} {D})
```

Finally, let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
open import Data.String using (String)

-- Any upper bound is fine but we are at least 2 deep.
cc_example_walk : ∀ {i : Size} → CCC (↑ ↑ i) String
cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

cc_example_walk_zoom : Variant ∞ String
cc_example_walk_zoom = ⟦ cc_example_walk ⟧ (λ {"Ekko" → 0; _ → 0})
```

Running this program shows that `cc_example_walk_zoom` indeed evaluates to the String `zoom`.
But we can also prove it:
```agda
_ : cc_example_walk_zoom ≡ Artifactᵥ "zoom" []
_ = refl
```

## Completeness

Proof in progress:

Idea: Show that we can embed any list of variants into a big choice.
Maybe its smarter to do this for ADDs and then to conclude by transitivity of translations that CCC is also complete.

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≗_)
open Eq.≡-Reasoning
open import Function using (id; _∘_)
open import Data.List.Properties using (map-∘; map-id; map-cong)

describe-variant : ∀ {i : Size} {A : 𝔸} → Variant i A → CCC i A
describe-variant (Artifactᵥ a vs) = Artifact a (map describe-variant vs)

---- Proof for preservation of describe-variant

{-|
Unfortunately, I had to surrender and just flag this function as terminating.
One solution to prove its termination is to use a sized variant (instead of using ∞).
The problem is that the semantics ⟦_⟧ forgets the size and sets it to ∞ and hence,
the types of v and ⟦ describe-variant v ⟧ c are different and hence their values can never be equivalent regarding ≡.
Below you find some tries of trying to circumvent these problems but so far I was not successfull.
-}
{-# TERMINATING #-}
describe-variant-preserves : ∀ {A} {c : Configuration}
  → (v : Variant ∞ A)
  → v ≡ ⟦ describe-variant v ⟧ c
describe-variant-preserves (Artifactᵥ _ []) = refl
describe-variant-preserves {c = c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
  begin
    e ∷ es
  ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
    map id (e ∷ es)
  ≡⟨ map-cong describe-variant-preserves (e ∷ es) ⟩
    map ((flip ⟦_⟧ c) ∘ describe-variant) (e ∷ es)
  ≡⟨ map-∘ {g = flip ⟦_⟧ c} {f = describe-variant} (e ∷ es) ⟩
    map (flip ⟦_⟧ c) (map describe-variant (e ∷ es))
  ∎)

{-|
Alternative definition of the semantics.
The function does exactly the same as ⟦_⟧ but remembers that 
-}
⟦_⟧-i : ∀ {i : Size} {A : 𝔸} → CCC i A → Configuration → Variant i A
⟦ Artifact a es ⟧-i c = Artifactᵥ a (map (flip ⟦_⟧-i c) es)
⟦ (D ⟨ alternatives ⟩) ⟧-i c = ⟦ choice-elimination (c D) alternatives ⟧-i c

describe-variant-preserves-i : ∀ {i} {A} {c : Configuration}
  → (v : Variant i A)
  → v ≡ ⟦ describe-variant v ⟧-i c
describe-variant-preserves-i (Artifactᵥ _ []) = refl
describe-variant-preserves-i {c = c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
  begin
    e ∷ es
  ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
    map id (e ∷ es)
  ≡⟨ map-cong describe-variant-preserves-i (e ∷ es) ⟩
    map ((flip ⟦_⟧-i c) ∘ describe-variant) (e ∷ es)
  ≡⟨ map-∘ {g = flip ⟦_⟧-i c} {f = describe-variant} (e ∷ es) ⟩
    map (flip ⟦_⟧-i c) (map describe-variant (e ∷ es))
  ∎)

semeq-choice : ∀ {i A} (e : CCC (↑ i) A) → (c : Configuration) → ⟦ e ⟧ c ≡ forget-variant-size (⟦ e ⟧-i c)
semeq-choice e c =
  begin
    ⟦ e ⟧ c
  ≡⟨ {!!} ⟩
    forget-variant-size (⟦ e ⟧-i c)
  ∎

sizeof : ∀ {i A} → CCC i A → Size
sizeof {i} _ = i

open Eq using (inspect; [_])

semeq : ∀ {i} {A}
  → (c : Configuration)
  → (e : CCC i A)
  → ⟦_⟧ {i} e c ≡ forget-variant-size {i} (⟦ e ⟧-i c)
semeq {i} {A} c (Artifact a es) =
  begin
    ⟦ Artifact a es ⟧ c
  ≡⟨⟩
    Artifactᵥ a (map (flip ⟦_⟧   c) es)
  ≡⟨ Eq.cong (Artifactᵥ a) (map-cong (semeq c) es) ⟩
    Artifactᵥ a (map (forget-variant-size ∘ (flip ⟦_⟧-i c)) es)
  ≡⟨ Eq.cong (Artifactᵥ a) (map-∘ es) ⟩
    Artifactᵥ a (map forget-variant-size (map (flip ⟦_⟧-i c) es))
  ≡⟨ sequence-forget-size (map (flip ⟦_⟧-i c) es) ⟩
    forget-variant-size (Artifactᵥ a (map (flip ⟦_⟧-i c) es))
  ≡⟨⟩
    forget-variant-size (⟦ Artifact a es ⟧-i c)
  ∎
  where mkArtifact : ∀ {j} → List (Variant j A) → Variant (↑ j) A
        mkArtifact = Artifactᵥ a
semeq {i} c (D ⟨ es ⟩) = {!!} --with choice-elimination (c D) es
--semeq-choice {i} (choice-elimination (c D) es) c
-- with choice-elimination (c D) es
-- ... | e | [ j ] =
--   begin
--     (⟦_⟧ e c)
--   ≡⟨ {!!} ⟩
--     (forget-variant-size (⟦_⟧-i e c))
--   ∎



-- describe-variant-preserves : ∀ {A} {c : Configuration}
--   → (v : Variant ∞ A)
--   → v ≡ ⟦ describe-variant v ⟧ c
-- describe-variant-preserves v = Eq.trans (describe-variant-preserves-i v) (Eq.sym (semeq _ (describe-variant v)))


```


## Utility

```agda
-- get all dimensions used in a CCC expression
open Data.List using (concatMap)

dims : ∀ {i : Size} {A : Set} → CCC i A → List Dimension
dims (Artifact _ es) = concatMap dims es
dims (D ⟨ es ⟩) = D ∷ concatMap dims (toList es)
```

## Show

```agda
open Data.String using (_++_)

show : ∀ {i : Size} → CCC i String → String
show (Artifact a []) = a
show (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (map show es)) ++ ">-"
show (D ⟨ es ⟩) = D ++ "⟨" ++ (Data.String.intersperse ", " (toList (map⁺ show es))) ++ "⟩"
```
