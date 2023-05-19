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
  Variant; Artifactᵥ;
  VarLang; FeatureLang; SelectionLang; VariabilityLanguage;
  Configuration; _∈_;
  Semantics;
  fromExpression; Artifactˡ)
open import Relations.Semantic using (_⊢_≣_; _⊆ᵥ_; _≚_)
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
We can encode a choice calculus expression without choices at the type level:
```agda
-- open import SemanticDomain using (Variant; Artifactᵥ)
```

An equivalent definition of semantics produces a configuration function `Config → Variant` that generates variants from configurations.
This definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags, according to Eric's phd thesis:
```agda
CCC-FeatureLang : FeatureLang
CCC-FeatureLang = Dimension

-- CCC-ConfLang : ConfLang
-- CCC-ConfLang = Dimension , Tag
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to introduce complex error handling and we cannot easily define a configuration to only produce tags within ranges.

```agda
open import Data.Fin.Base using (Fin)
open import Util.AuxProofs using (minFinFromLimit)

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

open import Data.List.Relation.Unary.All using (All; reduce; []; _∷_)
infix 5 _⊢_⟶_
data _⊢_⟶_ : ∀ {i : Size} {A : Domain}
  → Configuration Dimension Tag
  → (e : CCC i A)
  → Variant ∞ A
  → Set
  where

  S-Artifact : ∀ {A c j a} {es : List (CCC j A)}
    → (esᵥ : All (λ e → ∃[ v ] (c ⊢ e ⟶ v)) es)
      ---------------------------------------------------
    → c ⊢ Artifact a es ⟶ Artifactᵥ a (reduce proj₁ esᵥ)

  S-Choice : ∀ {A c j D} {n : ℕ} {es : List⁺ (CCC j A)} {v : Variant ∞ A}
    → (D , n) ∈ c
    → c ⊢ choice-elimination n es ⟶ v
      ---------------------------------
    → c ⊢ D ⟨ es ⟩ ⟶ v

deterministic : ∀ {A c i} {e : CCC i A} {v₁ v₂ : Variant ∞ A}
  → c ⊢ e ⟶ v₁
  → c ⊢ e ⟶ v₂
    ------------
  → v₁ ≡ v₂
deterministic (S-Artifact ls) (S-Artifact rs)  = {!!}
-- is not deterministic because configuration can currently map a Dimension to multiple values and we could pick any!
-- Could we?
deterministic (S-Choice {n = n} Dn∈c Dn⟶v₁) (S-Choice {n = m} Dm∈c Dm⟶v₂) = {!!}


{-|
Semantics of core choice calculus.
The semantic domain is a function that generates variants given configurations.
-}
⟦_⟧ : Semantics CCC Dimension Tag --
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ alternatives ⟩ ⟧ c = {!!} --⟦ choice-elimination (c D) alternatives ⟧ c

-- data ⟦_⟧ : ∀ {A : Domain} {i : Size} → CCC i A → CCC i A → Set where

CCCL : VariabilityLanguage
CCCL = record
  { expression = CCC
  ; fLang = Dimension
  ; sLang = Tag
  ; semantics = ⟦_⟧
  }
```

## Properties

Some transformation rules
```agda
-- -- unary choices are mandatory
-- D⟨e⟩≈e : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
--     --------------------------
--   → CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣ e
-- D⟨e⟩≈e = {!!}

-- -- other way to prove the above via variant-equivalence

-- D⟨e⟩⊆e : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
--     --------------------------
--   → fromExpression CCCL (D ⟨ e ∷ [] ⟩) ⊆ᵥ fromExpression CCCL e
-- D⟨e⟩⊆e config = ( config , refl )

-- e⊆D⟨e⟩ : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
--     --------------------------
--   → fromExpression e ⊆ᵥ fromExpression (D ⟨ e ∷ [] ⟩)
-- e⊆D⟨e⟩ config = ( config , refl )

-- D⟨e⟩≚e : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
--     --------------------------
--   → fromExpression (D ⟨ e ∷ [] ⟩) ≚ fromExpression e
-- D⟨e⟩≚e {i} {A} {e} {D} = D⟨e⟩⊆e {i} {A} {e} {D} , e⊆D⟨e⟩ {i} {A} {e} {D}

-- D⟨e⟩≚e' : ∀ {i : Size} {A : Set} {e : CCC i A} {D : Dimension}
--     ---------------
--   → D ⟨ e ∷ [] ⟩ ≚ e
-- D⟨e⟩≚e' {i} {A} {e} {D} =
--   ≣→≚ {↑ i} {i} {A}
--       {CCC} {Configuration} {⟦_⟧}
--       {D ⟨ e ∷ [] ⟩} {e}
--       (D⟨e⟩≈e {i} {A} {e} {D})
```

Finally, let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
open import Data.String using (String)

-- Any upper bound is fine but we are at least 2 deep.
-- cc_example_walk : ∀ {i : Size} → CCC (↑ ↑ i) String
-- cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

-- cc_example_walk_zoom : Variant String
-- cc_example_walk_zoom = ⟦ cc_example_walk ⟧ (λ {"Ekko" → 0; _ → 0})
```

Running this program shows that `cc_example_walk_zoom` indeed evaluates to the String `zoom`.
But we can also prove it:
```agda
-- _ : cc_example_walk_zoom ≡ Artifactᵥ "zoom" []
-- _ = refl
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

-- describe-variant : ∀ {i : Size} {A : Domain} → Variant i A → CCC ∞ A
-- describe-variant (Artifactᵥ a vs) = Artifact a (mapl describe-variant vs)

-- describe-variant-preserves : ∀ {i : Size} {A : Domain} {c : Configuration Dimension Tag}
--   → (v : Variant i A)
--   → v ≡ (⟦_⟧ {i} {A} (describe-variant {i} {A} v) c)
-- describe-variant-preserves (Artifactᵥ _ []) = refl
-- describe-variant-preserves {A} {c} (Artifactᵥ a (e ∷ es)) = Eq.cong (Artifactᵥ a) (
--   begin
--     e ∷ es
--   ≡⟨ Eq.sym (map-id (e ∷ es)) ⟩
--     mapl id (e ∷ es)
--   ≡⟨ map-cong (describe-variant-preserves) (e ∷ es) ⟩
--     mapl ((flip ⟦_⟧ c) ∘ describe-variant) (e ∷ es)
--   ≡⟨ map-∘ {g = flip ⟦_⟧ c} {f = describe-variant} (e ∷ es) ⟩
--     mapl (flip ⟦_⟧ c) (mapl describe-variant (e ∷ es))
--   ∎)

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
--   → (empty : A)
--   → (variants : List (Variant A))
--   → ∃[ e ∈ (CCC ∞ A)] (CCC , Configuration , ⟦_⟧ ⊢ e describes-all variants)
-- describe-variants z []       = Artifact z [] , []
-- describe-variants _ (v ∷ vs) = variant-choice (v ∷ vs) , variant-choice-describes-all (v ∷ vs)

-- -- todo use proper size
-- open import Data.Nat using (ℕ; suc; zero)
-- open import Data.Fin using (zero; toℕ; fromℕ)
-- open import SemanticDomain using (Variant)
open Definitions using (VSet)
open import Data.Multiset using (Multiset; _∈_; _≅_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

-- data _⟶_ : ∀ {A : Domain} {n : ℕ} → VSet n A → List⁺ (CCC ∞ A) → Set
-- infix 3 _⟶_
-- data _⟶_ where
--   E-single : ∀ {A : Domain} {vs : VSet zero A}
--       ----------------------------------------
--     → vs ⟶ describe-variant (vs zero) ∷ []

--   E-many : ∀ {A : Domain} {n : ℕ} {vs : VSet (suc n) A} {others : List⁺ (CCC ∞ A)}
--     → forget-last vs ⟶ others
--       ------------------------------------------------------------
--     → vs ⟶ describe-variant (vs (fromℕ (suc n))) ∷ toList others

-- naive-encoding : ∀ {A : Domain} {n : ℕ} → VSet n A → List⁺ (CCC ∞ A)
-- naive-encoding {n =  zero} vs = describe-variant (vs zero) ∷ []
-- naive-encoding {n = suc n} vs = describe-variant (vs (fromℕ (suc n))) ∷ toList (naive-encoding (forget-last vs))

-- naive-encoding-is-correct : ∀ {A} {n} {vs : VSet n A}
--   → vs ≅ ⟦ "D" ⟨ naive-encoding vs ⟩ ⟧
-- proj₁ (naive-encoding-is-correct {A} {zero} {vs}) zero with vs zero
-- ... | v =
--   let c = λ _ → zero
--    in c , (
--       begin
--         v
--       ≡⟨ describe-variant-preserves v ⟩
--         ⟦ describe-variant v ⟧ c
--       ≡⟨⟩
--         ⟦ choice-elimination zero (describe-variant v ∷ []) ⟧ c
--       ∎)
-- proj₁ (naive-encoding-is-correct {A} {suc n} {vs}) i with vs i
-- ... | v =
--   let n = toℕ i
--       c : String → ℕ
--       c = λ _ → n
--    in c , (
--       begin
--         v
--       ≡⟨ {!!} ⟩
--         ⟦ choice-elimination n (naive-encoding vs) ⟧ c
--       ≡⟨⟩
--         ⟦ "D" ⟨ naive-encoding vs ⟩ ⟧ c
--       ∎)
-- proj₂ (naive-encoding-is-correct {A} {n} {vs})     = {!!}

CCC-is-complete : Complete CCCL
CCC-is-complete vs = {!!} , {!!}

-- semfin : ∀ {i : Size} {A : Domain} → (e : CCC i A) → ∃[ n ] (Σ[ vs ∈ VSet n A ] (vs ≅ ⟦ e ⟧))
-- semfin e = {!!}


-- somehow combine semfin and naive-encoding-is-correct?
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
