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
open import Framework.Definitions
module Lang.CCC (Dimension : 𝔽) where
```

## Imports
```agda
-- -- Imports from Standard Library
open import Data.List
  using (List; []; _∷_; foldl; map)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to map⁺)
open import Data.Product
  using (_,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.Variants
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
import Construct.Choices as Chc
open Chc.VLChoiceₙ using () renaming (Syntax to Choiceₙ; Semantics to chc-sem)
open Chc.Choiceₙ using () renaming (Config to Configₙ)
```

## Syntax

```agda
data CCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (CCC i) A → CCC (↑ i) A
   chc  : ∀ {i A} → Choiceₙ Dimension (CCC i) A → CCC (↑ i) A

pattern _-<_>- a cs = atom (a At.-< cs >-)
pattern _⟨_⟩ D cs   = chc  (D Chc.Choiceₙ.⟨ cs ⟩)
```

## Semantics

Choice calculus has denotational semantics.
Semantics for choice calculus can be defined in different ways.
- As a set of pairs `Configuration × Variant`
- As a configuration function `Configuration → Variant` that generates variants from configurations.

The second definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags:
```agda
Configuration : 𝕂
Configuration = Configₙ Dimension
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to avoid complex error handling and we cannot easily define a configuration to only produce tags within ranges.
```agda
module Sem (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    CCCL : ∀ {i : Size} → VariabilityLanguage V
    CCCL {i} = ⟪ CCC i , Configuration , ⟦_⟧ ⟫

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V (Configₙ Dimension) (CCC i)
    ⟦ atom x ⟧ = PlainConstruct-Semantics Artifact-Construct mkArtifact CCCL x
    ⟦ chc  x ⟧ = chc-sem V Dimension CCCL id x
```

## Properties

Some transformation rules
```agda
module Properties (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  open import Framework.Variant V
  open import Framework.Relation.Expression V
  open Sem V mkArtifact

  module _ {A : 𝔸} where
    -- unary choices are mandatory
    D⟨e⟩≣e : ∀ {e : CCC ∞ A} {D : Dimension}
        -----------------------------
      → CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣₁ e
    D⟨e⟩≣e _ = refl

    -- other way to prove the above via variant-equivalence

    D⟨e⟩⊆e : ∀ {e : CCC ∞ A} {D : Dimension}
        -------------------------------
      → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≤ e
    D⟨e⟩⊆e c = c , refl

    e⊆D⟨e⟩ : ∀ {e : CCC ∞ A} {D : Dimension}
        -------------------------------
      → CCCL , CCCL ⊢ e ≤ D ⟨ e ∷ [] ⟩
    e⊆D⟨e⟩ c = c , refl

    D⟨e⟩≣e' : ∀ {e : CCC ∞ A} {D : Dimension}
        ------------------------------
      → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣ e
    D⟨e⟩≣e' {e} {D} = D⟨e⟩⊆e {e} {D} , e⊆D⟨e⟩ {e} {D}
```

## Completeness

Proof in progress:

Idea: Show that we can embed any list of variants into a big choice.
Maybe its smarter to do this for ADDs and then to conclude by transitivity of translations that CCC is also complete.

```agda
  -- import Relation.Binary.PropositionalEquality as Peq
  -- open Peq using (_≡_; refl; _≗_)
  -- open Peq.≡-Reasoning
  -- open import Function using (id; _∘_)
  -- open Data.List using (map)
  -- open import Data.List.Properties using (map-∘; map-id; map-cong)

  -- describe-variant : ∀ {i : Size} → V A → CCC i A
  -- describe-variant x = {!!}
  -- describe-variant (a -< vs >-) = Artifact a (map describe-variant vs)

  ---- Proof for preservation of describe-variant

  {-|
  Unfortunately, I had to flag this function as terminating.
  One solution to prove its termination is to use a sized variant (instead of using ∞).
  The problem is that the semantics ⟦_⟧ forgets the size and sets it to ∞ and hence,
  the types of v and ⟦ describe-variant v ⟧ c are different and hence their values can never be equivalent regarding ≡.

  Below there is an exact copy of this function (describe-variant-preserves-i) that is proven to terminate and that relies on an exact copy of the choice calculus semantics that produces a Variant i.

  So the function below indeed terminates but proving it within our framework became a _technical_ challenge (not a mathematical one) for which I found no solution yet.
  -}
  -- {-# TERMINATING #-}
  -- describe-variant-preserves : ∀ {A} {c : Configuration}
  --   → (v : V A)
  --   → v ≡ ⟦ describe-variant v ⟧ c
  -- describe-variant-preserves = ?
  -- describe-variant-preserves (_ -< [] >-) = ?
  -- describe-variant-preserves {c = c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
  --   begin
  --     e ∷ es
  --   ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
  --     map id (e ∷ es)
  --   ≡⟨ map-cong describe-variant-preserves (e ∷ es) ⟩
  --     map ((flip ⟦_⟧ c) ∘ describe-variant) (e ∷ es)
  --   ≡⟨ map-∘ {g = flip ⟦_⟧ c} {f = describe-variant} (e ∷ es) ⟩
  --     map (flip ⟦_⟧ c) (map describe-variant (e ∷ es))
  --   ∎)

  -- {-|
  -- Alternative definition of the semantics.
  -- The function does exactly the same as ⟦_⟧ but remembers that the produced variant does not grow in size.
  -- -}
  -- ⟦_⟧-i : ∀ {i : Size} {A : 𝔸} → CCC i A → Configuration → Variant i A
  -- ⟦ Artifact a es ⟧-i c = Artifactᵥ a (map (flip ⟦_⟧-i c) es)
  -- ⟦ (D ⟨ alternatives ⟩) ⟧-i c = ⟦ choice-elimination (c D) alternatives ⟧-i c

  -- describe-variant-preserves-i : ∀ {i} {A} {c : Configuration}
  --   → (v : Variant i A)
  --   → v ≡ ⟦ describe-variant v ⟧-i c
  -- describe-variant-preserves-i (Artifactᵥ _ []) = refl
  -- describe-variant-preserves-i {c = c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
  --   begin
  --     e ∷ es
  --   ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
  --     map id (e ∷ es)
  --   ≡⟨ map-cong describe-variant-preserves-i (e ∷ es) ⟩
  --     map ((flip ⟦_⟧-i c) ∘ describe-variant) (e ∷ es)
  --   ≡⟨ map-∘ {g = flip ⟦_⟧-i c} {f = describe-variant} (e ∷ es) ⟩
  --     map (flip ⟦_⟧-i c) (map describe-variant (e ∷ es))
  --   ∎)

  sizeof : ∀ {i A} → CCC i A → Size
  sizeof {i} _ = i
```


## Utility

```agda
-- get all dimensions used in a CCC expression
open Data.List using (concatMap)

dims : ∀ {i : Size} {A : Set} → CCC i A → List Dimension
dims (_ -< es >-) = concatMap dims es
dims (D ⟨ es ⟩) = D ∷ concatMap dims (toList es)
```

## Show

```agda
open import Data.String using (String; _++_)

show : ∀ {i} → (Dimension → String) → CCC i String → String
show _ (a -< [] >-) = a
show show-D (a -< es@(_ ∷ _) >- ) = a ++ "-<" ++ (foldl _++_ "" (map (show show-D) es)) ++ ">-"
show show-D (D ⟨ es ⟩) = show-D D ++ "⟨" ++ (Data.String.intersperse ", " (toList (map⁺ (show show-D) es))) ++ "⟩"
```
