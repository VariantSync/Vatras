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
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat
  using (ℕ; suc; NonZero)
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
open import Lang.Annotation.Name using (Dimension)
open import Definitions using (
  Domain;
  Variant; Artifactᵥ; VSet; forget-last; VariantSetoid;
  VarLang; ConfLang; VariabilityLanguage;
  Semantics;
  fromExpression; Artifactˡ;
  forget-variant-size)
open import Relations.Semantic using (_⊢_≣_; _,_⊢_⊆ᵥ_; _,_⊢_≚_; ≣→≚)

open import Util.List using (lookup-clamped)
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

data CCC : VarLang where
  Artifact : Artifactˡ CCC
  _⟨_⟩ : ∀ {i : Size} {A : Domain} →
    Dimension → List⁺ (CCC i A) → CCC (↑ i) A
```

Smart constructors for plain artifacts.
Any upper bound is fine but we are at least 1 deep.
```agda
leaf : ∀ {i : Size} {A : Domain} → A → CCC (↑ i) A
leaf a = Artifact a []

leaves : ∀ {i : Size} {A : Domain} → List⁺ A → List⁺ (CCC (↑ i) A)
leaves = mapl⁺ leaf

-- upcast : ∀ {i : Size} {j : Size< i} {A : Domain} → CCC j A → CCC i A
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
Configuration : ConfLang
Configuration = Dimension → Tag
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to introduce complex error handling and we cannot easily define a configuration to only produce tags within ranges.

```agda
-- Selects the alternative at the given tag.
-- Agda can implicitly prove that the length of the list is positive, because it is a non-empty list, and by type inference, it supplies the list length to clampWithin.
choice-elimination : {A : Domain} → Tag → List⁺ A → A
choice-elimination = lookup-clamped

{-|
Semantics of core choice calculus.
The semantic domain is a function that generates variants given configurations.
-}
-- ⟦_⟧ : ∀ {i : Size} {A : Domain} → CCC i A → Configuration → Variant i A
⟦_⟧ : Semantics CCC Configuration
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ (D ⟨ alternatives ⟩) ⟧ c = ⟦ choice-elimination (c D) alternatives ⟧ c

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
    --------------------------
  → CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣ e
D⟨e⟩≣e = refl

-- -- other way to prove the above via variant-equivalence

D⟨e⟩⊆e : ∀ {i : Size} {A : Domain} {e : CCC i A} {D : Dimension}
    -------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ⊆ᵥ e
D⟨e⟩⊆e config = ( config , refl )

e⊆D⟨e⟩ : ∀ {i : Size} {A : Domain} {e : CCC i A} {D : Dimension}
    -------------------------------
  → CCCL , CCCL ⊢ e ⊆ᵥ D ⟨ e ∷ [] ⟩
e⊆D⟨e⟩ config = ( config , refl )

D⟨e⟩≚e : ∀ {i : Size} {A : Domain} {e : CCC i A} {D : Dimension}
    ------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≚ e
D⟨e⟩≚e {i} {A} {e} {D} = D⟨e⟩⊆e {i} {A} {e} {D} , e⊆D⟨e⟩ {i} {A} {e} {D}

D⟨e⟩≚e' : ∀ {i : Size} {A : Domain} {e : CCC i A} {D : Dimension}
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
open import Data.List.Relation.Unary.All using (All; []; _∷_; construct; fromList)
open import Lang.Properties.Completeness using (Incomplete; Complete)
open Data.Product using (proj₁; proj₂)
open import Util.Existence using (_,_)
open Size using (∞)
open Data.Product using (_×_)
open import Data.List.Properties using (map-id; map-cong; map-∘)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

open Function using (_∘_; id)

open import Axioms.Extensionality using (extensionality; ≗→≡)

import Data.Multiset
open import Lang.Properties.NonEmpty

describe-variant : ∀ {i : Size} {A : Domain} → Variant i A → CCC i A
describe-variant (Artifactᵥ a vs) = Artifact a (mapl describe-variant vs)

-- describe-variant-preserves : ∀ {i : Size} {A : Domain} {c : Configuration}
--   → (v : Variant i A)
--   → v ≡ ⟦ describe-variant v ⟧ c
-- describe-variant-preserves (Artifactᵥ _ []) = refl
-- describe-variant-preserves {_} {_} {c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
--   begin
--     e ∷ es
--   ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
--     mapl id (e ∷ es)
--   ≡⟨ map-cong (describe-variant-preserves) (e ∷ es) ⟩
--     mapl ((flip ⟦_⟧ c) ∘ describe-variant) (e ∷ es)
--   ≡⟨ map-∘ {g = flip ⟦_⟧ c} {f = describe-variant} (e ∷ es) ⟩
--     mapl (flip ⟦_⟧ c) (mapl describe-variant (e ∷ es))
--   ∎)

-- CCCL-is-NonEmpty : NonEmpty CCCL
-- CCCL-is-NonEmpty = record
--   { describe = describe-variant
--   ; describe-preserves = λ v → any-conf , {!!} --describe-variant-preserves {c = any-conf} v
--   } where any-conf = λ _ → 0

-- indexed : ∀ {A : Set} → ℕ → List A → List (ℕ × A)
-- indexed _     [] = []
-- indexed start (x ∷ xs) = (start , x) ∷ indexed (suc start) xs

-- variant-choice : ∀ {A : Set} → List⁺ (Variant A) → CCC ∞ A
-- variant-choice vs = "D" ⟨ mapl⁺ describe-variant vs ⟩

-- -- TODO: Prove this instead of postulating it
-- postulate
--   variant-choice-describes-all : ∀ {A : Set}
--     → (vs : List⁺ (Variant A))
--       -------------------------------------------------------------------------
--     → CCC , Configuration , ⟦_⟧ ⊢ (variant-choice vs) describes-all (toList vs)

-- describe-variants : ∀ {A : Domain}
--   → (variants : List (Variant A))
--   → ∃[ e ∈ (CCC ∞ A)] (CCC , Configuration , ⟦_⟧ ⊢ e describes-all variants)
-- describe-variants z []       = Artifact z [] , []
-- describe-variants _ (v ∷ vs) = variant-choice (v ∷ vs) , variant-choice-describes-all (v ∷ vs)

-- -- todo use proper size
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (zero; toℕ; fromℕ)

-- data _⟶_ : ∀ {A : Domain} {n : ℕ} → VSet A n → List⁺ (CCC ∞ A) → Set
-- infix 3 _⟶_
-- data _⟶_ where
--   E-single : ∀ {A : Domain} {vs : VSet A zero}
--       ----------------------------------------
--     → vs ⟶ describe-variant (vs zero) ∷ []

--   E-many : ∀ {A : Domain} {n : ℕ} {vs : VSet A (suc n)} {others : List⁺ (CCC ∞ A)}
--     → forget-last vs ⟶ others
--       ------------------------------------------------------------
--     → vs ⟶ describe-variant (vs (fromℕ (suc n))) ∷ toList others

naive-encoding : ∀ {A : Domain} {n : ℕ} → VSet A n → List⁺ (CCC ∞ A)
naive-encoding {n =  zero} vs = describe-variant (vs zero) ∷ []
naive-encoding {n = suc n} vs = describe-variant (vs (fromℕ (suc n))) ∷ toList (naive-encoding (forget-last vs))

-- module Completeness {A : Domain} where
--   open Data.Multiset (VariantSetoid ∞ A) using (_≅_; _∈_)

--   naive-encoding-is-correct : ∀ {n} {vs : VSet A n}
--     → vs ≅ ⟦ "D" ⟨ naive-encoding vs ⟩ ⟧
--   proj₁ (naive-encoding-is-correct {zero} {vs}) zero with vs zero
--   ... | v =
--     let c = λ _ → zero
--     in c , (
--         begin
--           v
--         ≡⟨ describe-variant-preserves v ⟩
--           ⟦ describe-variant v ⟧ c
--         ≡⟨⟩
--           ⟦ choice-elimination zero (describe-variant v ∷ []) ⟧ c
--         ∎)
--   proj₁ (naive-encoding-is-correct {suc n} {vs}) i with vs i
--   ... | v =
--     let n = toℕ i
--         c : String → ℕ
--         c = λ _ → n
--     in c , (
--         begin
--           v
--         ≡⟨ {!!} ⟩
--           ⟦ choice-elimination n (naive-encoding vs) ⟧ c
--         ≡⟨⟩
--           ⟦ "D" ⟨ naive-encoding vs ⟩ ⟧ c
--         ∎)
--   proj₂ (naive-encoding-is-correct {zero} {vs}) = {!!}
--   proj₂ (naive-encoding-is-correct {suc n} {vs}) c = {!!}


CCC-is-complete : Complete CCCL
CCC-is-complete {n = n} vs = fromExpression CCCL ("D" ⟨ naive-encoding vs ⟩) , {!!}
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
show (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl show es)) ++ ">-"
show (D ⟨ es ⟩) = D ++ "⟨" ++ (Data.String.intersperse ", " (toList (mapl⁺ show es))) ++ "⟩"
```
