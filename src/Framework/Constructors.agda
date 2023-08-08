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

-- the annotation (or feature) language
𝔽 : Set₁
𝔽 = Set

-- Selections: the semantic domain of a feature language
𝕊 : Set₁
𝕊 = Set

-- configurations: A configuration assigns
record Config (F : 𝔽) (S : 𝕊) : Set where
  field
    lookup : F → S
open Config public

-- an annotation language
𝕃 : Set₁
𝕃 = 𝔸 → Set

𝕍 : Set₁
𝕍 = 𝔸 → Set

Syntax : Set₁
Syntax = 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set

-- constructor arguments
CArg : Set₁
CArg = 𝕃 → 𝔸 → Set

-- constructors (or grammar rules) for annotation langauges
Constructor : CArg → 𝕃 → Set₁
Constructor P L = ∀ {A : 𝔸} → P L A → L A

-- private
--   variable
--     S : 𝕊
--     F : 𝔽
--     L : 𝕃
--     A : 𝔸

data Variant (A : 𝔸) : Set where
  Node : A → List (Variant A) → Variant A

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

Semantics : 𝕍 → 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set
Semantics V F S L A = L A → Config F S → V A



record Language (V : 𝕍) : Set₁ where
  field
    annotation-language : 𝔽
    selection-set : 𝕊
    constructor-set : 𝕃
    semantics : ∀ {A : 𝔸} → Semantics V annotation-language selection-set constructor-set A
open Language public

record Rule (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  field
    syn : Syntax
    sem :
      ∀ {A : 𝔸}
      → (L : 𝕃)
      → Semantics V F S L A
      → syn F S L A
      → Config F S
      → V A

Specialized-Syntax : Set₁
Specialized-Syntax = 𝔸 → Set

Specialized-Rule : (V : 𝕍) → Language V → Set₁
Specialized-Rule V L = Rule V (annotation-language L) (selection-set L)

Cons : ∀ {V : 𝕍} (L : Language V) → Specialized-Syntax → Set₁
Cons L R = ∀ {A : 𝔸} → R A → constructor-set L A

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

data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} → A → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} → GrulerVariant A → GrulerVariant A → GrulerVariant A

sem-leaf : ∀ {A : 𝔸} {L : Language GrulerVariant}
  → Leaf A
  → Config (annotation-language L) (selection-set L) -- irrelevant argument
  → GrulerVariant A
sem-leaf (leaf a) _ = asset a

sem-pc : ∀ {F : 𝔽} {S : 𝕊} {L : 𝕃} {A : 𝔸}
  → Semantics GrulerVariant F S L A
  → ParallelComposition L A
  → Config F S
  → GrulerVariant A
sem-pc ⟦_⟧ᵢ (l ∥ r) c = ⟦ l ⟧ᵢ c ∥ ⟦ r ⟧ᵢ c

sem-bc : ∀ {F : 𝔽} {L : 𝕃} {A : 𝔸}
  → Semantics GrulerVariant F Bool L A
  → BinaryChoice F L A
  → Config F Bool
  → GrulerVariant A
sem-bc ⟦_⟧ᵢ (D ⟨ l , r ⟩) c = ⟦ if lookup c D then l else r ⟧ᵢ c

data Gruler : 𝕃 where
  GAsset    : ∀ {A : 𝔸} → Leaf A                       → Gruler A
  GArtifact : ∀ {A : 𝔸} → ParallelComposition Gruler A → Gruler A
  GChoice   : ∀ {A : 𝔸} → BinaryChoice ℕ Gruler A      → Gruler A

-- This functions can be computed from the semantics of all languages above.
-- I have no idea whether this is feasible within Agda though.
{-# TERMINATING #-}
⟦_⟧ᵍ : ∀ {A : 𝔸}
  → Gruler A
  → Config ℕ Bool
  → GrulerVariant A
⟦ GAsset A ⟧ᵍ = sem-leaf A
⟦ GArtifact PC ⟧ᵍ = sem-pc ⟦_⟧ᵍ PC
⟦ GChoice C ⟧ᵍ = sem-bc ⟦_⟧ᵍ C

cc : ∀ (F : 𝔽) → Rule GrulerVariant F Bool
cc _ = record
  { syn = λ F _ L A → BinaryChoice F L A
  ; sem = λ L → sem-bc {L = L}
  }

Leaf-Rule : ∀ (F : 𝔽) (S : 𝕊) → Rule GrulerVariant F S
Leaf-Rule _ _ = record
  { syn = λ _ _ _ → Leaf
  ; sem = sem-leaf
  }

Gruler-Language : Language GrulerVariant
Gruler-Language = record
  { annotation-language = ℕ
  ; selection-set       = Bool
  ; constructor-set     = Gruler
  ; semantics           = λ e → ⟦ e ⟧ᵍ
  }

make-leaf :
  ∀ (L : Language GrulerVariant) → Cons L Leaf
  → {A : 𝔸} → A → (constructor-set L A)
make-leaf _ make-artifact a = make-artifact (leaf a)

make-choice :
  ∀ {V : 𝕍} {A : 𝔸}
  → (L : Language V) → Cons L (BinaryChoice (annotation-language L) L A)
  → (annotation-language L)
  → {A : 𝔸} → (constructor-set L A) → (constructor-set L A)
  → (constructor-set L A)
make-choice = ?

make-gruler-leaf : ∀ {A : 𝔸} → A → Gruler A
make-gruler-leaf = make-leaf Gruler-Language GAsset

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
