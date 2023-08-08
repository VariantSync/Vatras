{-# OPTIONS --sized-types #-}
module Framework.Constructors where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Annotation.Name using (Name)

import Data.IndexedSet

-- some atomic data
𝔸 : Set₁
𝔸 = Set

-- Annotation Language
𝔽 : Set₁
𝔽 = Set

-- Selections language (the semantic domain of a feature language 𝔽)
𝕊 : Set₁
𝕊 = Set

-- Variability Language
𝕃 : Set₁
𝕃 = 𝔸 → Set

-- Variant Language
𝕍 : Set₁
𝕍 = 𝔸 → Set

-- configurations: A configuration is anything that allows us to do a lookup
record Config (F : 𝔽) (S : 𝕊) : Set where
  field
    lookup : F → S
open Config public

Syntax : Set₁
Syntax = 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set

Semantics : 𝕍 → 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set
Semantics V F S L A = L A → Config F S → V A

-- constructor arguments
-- CArg : Set₁
-- CArg = 𝕃 → 𝔸 → Set

-- constructors (or grammar rules) for annotation langauges
-- Constructor : CArg → 𝕃 → Set₁
-- Constructor P L = ∀ {A : 𝔸} → P L A → L A

-- record Cons (L : 𝕃) (A : 𝔸) : Set₁ where
--   inductive
--   field
--     val : L A
--     sem : ∀ {A : 𝔸} → syn A → Variant A
-- open Cons public

-- record Arti (A : 𝔸) : Set₁ where
--   field
--     val : A
--     child : Σ[ syn ∈ Syntax ] (Cons syn A)

-- ArtiCons : ∀ {A : 𝔸} → Cons Arti A
-- ArtiCons = record
--   { syn = {!!}
--   ; sem = {!!} }

-- record Artifact (S : 𝕊) (F : 𝔽) (L : 𝕃) (A : 𝔸) : Set₁ where
  -- inductive
  -- constructor _-<_>-
  -- field
    -- value : A
    -- children : List (Cons S F L A)

-- ArtifactCons : (S : 𝕊) (F : 𝔽) (L : 𝕃) (A : 𝔸) → Cons S F L A
-- ArtifactCons S F L A = record
--   { syn = Artifact
--   ; sem = {!!}
--   }

record Language (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  field
    constructor-set : 𝕃
    semantics : ∀ {A : 𝔸} → Semantics V F S constructor-set A
open Language public

record Rule (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  field
    syn : Syntax
    sem :
      ∀ {A : 𝔸}
      → (L : Language V F S)
      → syn F S (constructor-set L) A
      → Config F S
      → V A

Specialized-Syntax : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → (L : Language V F S) → Syntax → Set₁
Specialized-Syntax {_} {F} {S} L Syn = (A : 𝔸) → Syn F S (constructor-set L) A

Specialized-Rule : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → Language V F S → Set₁
Specialized-Rule {V} {F} {S} _ = Rule V F S

-- Actually, we do not need a whole rule as input here because we are using only its syntax.
-- But it is nice to use because currently, it is the creation of a rule at which point is decided
-- which arguments of the syntax are optional and which not (from (constructor-set L), F, and S).
Cons : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → (L : Language V F S) → Specialized-Rule L → Set₁
Cons {_} {F} {S} L R = ∀ {A : 𝔸} → Rule.syn R F S (constructor-set L) A → constructor-set L A

-- Cons : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → (L : Language V F S) → Specialized-Syntax L → Set₁
-- Cons {_} {F} {S} L R = ∀ {A : 𝔸} → Rule.syn R F S (constructor-set L) A → constructor-set L A

data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} → A → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} → GrulerVariant A → GrulerVariant A → GrulerVariant A

---- SYNTAX ----

-- record Leaf : Syntax where
record Leaf (A : 𝔸) : Set where
  constructor leaf
  field
    val : A

record ParallelComposition (L : 𝕃) (A : 𝔸) : Set where
  constructor _∥_
  field
    l : L A
    r : L A

record BinaryChoice (F : 𝔽) (L : 𝕃) (A : 𝔸) : Set where
  constructor _⟨_,_⟩
  field
    D : F
    l : L A
    r : L A

---- SEMANTICS ----

Leaf-Semantics : ∀ {A : 𝔸} {F : 𝔽} {S : 𝕊}
  → (L : Language GrulerVariant F S)
  → Leaf A
  → Config F S -- irrelevant argument
  → GrulerVariant A
Leaf-Semantics _ (leaf a) _ = asset a

ParallelComposition-Semantics : ∀ {A : 𝔸} {F : 𝔽} {S : 𝕊}
  → (L : Language GrulerVariant F S)
  → ParallelComposition (constructor-set L) A
  → Config F S
  → GrulerVariant A
ParallelComposition-Semantics L (l ∥ r) c = ⟦ l ⟧ᵢ c ∥ ⟦ r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

Binary-Choice-Semantics : ∀ {V : 𝕍} {A : 𝔸} {F : 𝔽}
  → (L : Language V F Bool)
  → BinaryChoice F (constructor-set L) A
  → Config F Bool
  → V A
Binary-Choice-Semantics L (D ⟨ l , r ⟩) c = ⟦ if lookup c D then l else r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

---- RULES ----

Leaf-Rule : ∀ (F : 𝔽) (S : 𝕊) → Rule GrulerVariant F S
Leaf-Rule _ _ = record
  { syn = λ _ _ _ → Leaf
  ; sem = Leaf-Semantics
  }

ParallelComposition-Rule : ∀ (F : 𝔽) (S : 𝕊) → Rule GrulerVariant F S
ParallelComposition-Rule _ _ = record
  { syn = λ _ _ → ParallelComposition
  ; sem = ParallelComposition-Semantics
  }

BinaryChoice-Rule : ∀ (V : 𝕍) (F : 𝔽) → Rule V F Bool
BinaryChoice-Rule _ _ = record
  { syn = λ F _ → BinaryChoice F
  ; sem = Binary-Choice-Semantics
  }

data Gruler : 𝕃 where
  GAsset    : ∀ {A : 𝔸} → Leaf A                       → Gruler A
  GArtifact : ∀ {A : 𝔸} → ParallelComposition Gruler A → Gruler A
  GChoice   : ∀ {A : 𝔸} → BinaryChoice ℕ Gruler A      → Gruler A

-- This functions can be computed from the semantics of all languages above.
-- I have no idea whether this is feasible within Agda though.
{-# TERMINATING #-}
⟦_⟧ᵍ : ∀ {A : 𝔸} → Semantics GrulerVariant ℕ Bool Gruler A

Gruler-Language : Language GrulerVariant ℕ Bool
Gruler-Language = record
  { constructor-set = Gruler
  ; semantics       = ⟦_⟧ᵍ
  }

⟦ GAsset A     ⟧ᵍ = Leaf-Semantics Gruler-Language A
⟦ GArtifact PC ⟧ᵍ = ParallelComposition-Semantics Gruler-Language PC
⟦ GChoice C    ⟧ᵍ = Binary-Choice-Semantics Gruler-Language C

make-leaf : ∀ {F : 𝔽} {S : 𝕊}
  → (L : Language GrulerVariant F S) → Cons L (Leaf-Rule F S)
  → {A : 𝔸} → A → (constructor-set L A)
make-leaf _ cons-leaf a = cons-leaf (leaf a)

make-choice : ∀ {V : 𝕍} {F : 𝔽}
  → (L : Language V F Bool) → Cons L (BinaryChoice-Rule V F)
  → F
  → {A : 𝔸} → (constructor-set L A) → (constructor-set L A)
  → (constructor-set L A)
make-choice L cons-choice D l r = cons-choice (D ⟨ l , r ⟩)

make-gruler-leaf : ∀ {A : 𝔸} → A → Gruler A
make-gruler-leaf = make-leaf Gruler-Language GAsset

make-gruler-choice : ∀ {A : 𝔸} → ℕ → Gruler A → Gruler A → Gruler A
make-gruler-choice n = make-choice Gruler-Language GChoice n

-- record Choice (L : 𝕃) (A : 𝔸) : Set where
--   constructor _⟨_⟩
--   field
--     name : Name
--     alternatives : List⁺ (L A)

-- record Option (L : 𝕃) (A : 𝔸) : Set where
--   constructor _〔_〕
--   field
--     name : Name
--     child : L A

-- data Variant : 𝕃 where
--   Artifactᵥ : ∀ {A : 𝔸} → Artifact Variant A → Variant A
-- data CCₙ : 𝕃 where
--   Artifactₙ : ∀ {A : 𝔸} → Artifact CCₙ A → CCₙ A
--   Choiceₙ : ∀ {A : 𝔸} → Choice CCₙ A → CCₙ A

-- data OC : 𝕃 where
--   Artifactₒ : ∀ {A : 𝔸} → Artifact OC A → OC A
--   Optionₒ : ∀ {A : 𝔸} → Option OC A → OC A

-- Semantics : ℂ → 𝕃 → Set₁
-- Semantics C L = ∀ {A : 𝔸} → L A → C → Variant A

-- VariantSetoid : 𝔸 → Setoid 0ℓ 0ℓ
-- VariantSetoid A = Eq.setoid (Variant A)

-- IndexedVMap : 𝔸 → Set → Set
-- IndexedVMap A I = IndexedSet I
--   where open Data.IndexedSet (VariantSetoid A) using (IndexedSet)

-- {-|
-- Variant maps constitute the semantic domain of variability languages.
-- While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
-- via Fin (suc n) here for convenience.
-- -}
-- VMap : 𝔸 → ℕ → Set
-- VMap A n = IndexedVMap A (Fin (suc n))

-- Complete : (C : ℂ) → (L : 𝕃) → Semantics C L → Set₁
-- Complete C L ⟦_⟧ = ∀ {A n}
--   → (vs : VMap A n)
--     ----------------------------------
--   → Σ[ e ∈ L A ]
--       (let open Data.IndexedSet (VariantSetoid A) using (_≅_)
--         in vs ≅ ⟦ e ⟧)

-- -- any language with artifacts and choices is complete
-- choices-make-complete :
--   ∀ (C : ℂ) (L : 𝕃) (S : Semantics C L)
--   → Constructor Artifact L
--   → Constructor Choice L
--   → Complete C L S
-- -- TODO: Reuse the proof that variant lists are complete. Then show that
-- --       every language with at least artifacts and choices is at least
-- --       as expressive as a variant list.
-- choices-make-complete C L ⟦_⟧ mkArtifact mkChoice vs = {!!}

-- binary-to-nary-choice :
--   ∀ {L₁ L₂ A}
--   → (translation : L₁ A → L₂ A)
--   → BinaryChoice L₁ A
--   → Choice L₂ A
-- binary-to-nary-choice t (D ⟨ l , r ⟩) = D ⟨ t l ∷ t r ∷ [] ⟩

-- module _ {A : 𝔸} where
  -- open Data.IndexedSet (VariantSetoid A) using (_≅_)

  -- binary-to-nary-choice-preserves :
  --   ∀ {L₁ L₂ : 𝕃}
  --   → {C₁ C₂ : ℂ}
  --   → {⟦_⟧₁ : Semantics C₁ L₁}
  --   → {⟦_⟧₂ : Semantics C₂ L₂}
  --   → (mkChoice₁ : Constructor BinaryChoice L₁)
  --   → (mkChoice₂ : Constructor Choice L₂)
  --   → (t : L₁ A → L₂ A)
  --   → (D : Name)
  --   → (l r : L₁ A)
  --   → ⟦ l ⟧₁ ≅ ⟦ t l ⟧₂
  --   → ⟦ r ⟧₁ ≅ ⟦ t r ⟧₂
  --   → ⟦ mkChoice₁ (D ⟨ l , r ⟩) ⟧₁ ≅ ⟦ mkChoice₂ (binary-to-nary-choice {L₁} {L₂} t (D ⟨ l , r ⟩)) ⟧₂
  -- binary-to-nary-choice-preserves mkChoice₁ mkChoice₂ t D l r t-pres-l t-pres-r =
  --   (λ c₁ → {!!} Data.Product., {!!}) Data.Product., {!!}
  --   -- This is unprovable yet.
  --   -- We have no assumptions on semantics and configurations, so we can neither
  --   -- translate configurations nor show that this translation indeed preserves
  --   -- the semantics, which in turn could do anything as a black box function.
  --   -- We need a way to manipulate the configuration to specify what to do for the new dimensions.
  --   -- We need a way to perform lookups in configurations to evaluate the semantics.

-- artifact-translation :
--   ∀ {L₁ L₂ A}
--   → (translation : L₁ A → L₂ A)
--   → Artifact L₁ A
--   → Artifact L₂ A
-- artifact-translation t (a -< es >-) = a -< map t es >-

-- module _ {A : 𝔸} where
--   open import Data.List.Relation.Unary.All using (All)
--   open Data.IndexedSet (VariantSetoid A) using (_≅_)
--   open Data.Product using (_,_)

--   artifact-translation-preserves :
--     ∀ {L₁ L₂ : 𝕃}
--     → {C₁ C₂ : ℂ}
--     → {⟦_⟧₁ : Semantics C₁ L₁}
--     → {⟦_⟧₂ : Semantics C₂ L₂}
--     → (mkArtifact₁ : Constructor Artifact L₁)
--     → (mkArtifact₂ : Constructor Artifact L₂)
--     → (t : L₁ A → L₂ A)
--     → (a : A)
--     → (es : List (L₁ A))
--     → (All (λ e → ⟦ e ⟧₁ ≅ ⟦ t e ⟧₂) es)
--     → ⟦ mkArtifact₁ (a -< es >-) ⟧₁ ≅ ⟦ mkArtifact₂ (artifact-translation {L₁} {L₂} t (a -< es >-)) ⟧₂
--   artifact-translation-preserves mkArtifact₁ mkArtifact₂ t a es t-preserves-es = {!!}
--   -- Proving this is actually quite hard. We again need the traversable over configurations somehow.
--   -- Instead of continuing to prove this, we should try to use it:
--   -- What would be the benfit of having this proof?
--   -- Would it really avoid duplication and would it help us for proofs of expressiveness?
--   -- Also proving the preservation of binary-to-nary-choice might be easier.

-- {-# TERMINATING #-}
-- CC₂→CCₙ : ∀ {A} → CC₂ A → CCₙ A
-- CC₂→CCₙ (Artifact₂ a) = Artifactₙ (artifact-translation CC₂→CCₙ a)
-- CC₂→CCₙ (Choice₂ c) = Choiceₙ (binary-to-nary-choice CC₂→CCₙ c)

-- Examples on how to use constructors to make functions that abstract over languages.
-- leaf :
  -- ∀ {L : 𝕃} → Constructor Artifact L
  -- → {A : 𝔸} → (a : A)
  -- → L A
-- leaf mkArtifact a = mkArtifact (a -< [] >-)

-- variant-leaf : ∀ {A : 𝔸} (a : A) → Variant A
-- variant-leaf = leaf Artifactᵥ

-- cc₂-leaf : ∀ {A : 𝔸} (a : A) → CC₂ A
-- cc₂-leaf = leaf Artifact₂
