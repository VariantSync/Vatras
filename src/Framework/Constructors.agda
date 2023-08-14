{-# OPTIONS --sized-types #-}
module Framework.Constructors where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)

open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Annotation.Name using (Name)

import Data.IndexedSet

-- some atomic data
𝔸 : Set₁
𝔸 = Set

private
  variable
    A : 𝔸

-- Variability Language
𝕃 : Set₁
𝕃 = 𝔸 → Set

-- Variant Language
𝕍 : Set₁
𝕍 = 𝔸 → Set

-- Constructor Type
ℂ : Set₁
ℂ = 𝔸 → Set

-- Annotation Language
𝔽 : Set₁
𝔽 = Set

-- Selections Language (the semantic domain of an annotation language 𝔽)
𝕊 : Set₁
𝕊 = Set

-- Configurations: A configuration is anything that allows us to do a lookup.
record Config (F : 𝔽) (S : 𝕊) : Set where
  field
    lookup : F → S
open Config public

-- Semantics of variability languages
𝕃-Semantics : 𝕍 → 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set
𝕃-Semantics V F S L A = L A → Config F S → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  field
    expressions : 𝕃
    semantics   : 𝕃-Semantics V F S expressions A
open VariabilityLanguage public

-- Semantics of constructors
ℂ-Semantics : 𝕍 → 𝔽 → 𝕊 → (𝕃 → ℂ) → 𝔸 → Set₁
ℂ-Semantics V F S C A = (L : VariabilityLanguage V F S) → C (expressions L) A → Config F S → V A

record _∈_ (Constructor : ℂ) (Expression : 𝕃) : Set₁ where
  field
    cons : Constructor A → Expression A
    snoc : Expression  A → Maybe (Constructor A)
    id-l : snoc {A} ∘ cons {A} ≗ just
open _∈_ public

_∉_ : ℂ → 𝕃 → Set₁
C ∉ L = ¬ (C ∈ L)

_⊆_ : 𝕃 → 𝕃 → Set₁
L₁ ⊆ L₂ = ∀ (C : ℂ) → C ∈ L₁ → C ∈ L₂

_≅_ : 𝕃 → 𝕃 → Set₁
L₁ ≅ L₂ = L₁ ⊆ L₂ × L₂ ⊆ L₁

----- EXAMPLES FOR VARIANT TYPES -----

data GrulerVariant : 𝕍 where
  asset : A → GrulerVariant A
  _∥_   : GrulerVariant A → GrulerVariant A → GrulerVariant A

---- EXAMPLES FOR CONSTRUCTORS ----

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

Leaf-Semantics : ∀ {F : 𝔽} {S : 𝕊} {A : 𝔸}
  → ℂ-Semantics GrulerVariant F S (λ _ → Leaf) A
Leaf-Semantics _ (leaf a) _ = asset a

ParallelComposition-Semantics : ∀ {F : 𝔽} {S : 𝕊} {A : 𝔸}
  → ℂ-Semantics GrulerVariant F S ParallelComposition A
ParallelComposition-Semantics L (l ∥ r) c = ⟦ l ⟧ᵢ c ∥ ⟦ r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

Binary-Choice-Semantics : ∀ {V : 𝕍} {F : 𝔽} {A : 𝔸}
  → ℂ-Semantics V F Bool (BinaryChoice F) A
Binary-Choice-Semantics L (D ⟨ l , r ⟩) c = ⟦ if lookup c D then l else r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

---- EXAMPLE : Gruler's language -----
-- All these language implementations are super straighforward and could in fact be generated if Agda would have macros!
data Gruler : 𝕃 where
  GAsset  : Leaf A                       → Gruler A
  GPComp  : ParallelComposition Gruler A → Gruler A
  GChoice : BinaryChoice ℕ Gruler A      → Gruler A

-- I have no idea how we could prove this terminating but let's just avoid that headache.
{-# TERMINATING #-}
⟦_⟧ᵍ : 𝕃-Semantics GrulerVariant ℕ Bool Gruler A

GrulerVL : VariabilityLanguage GrulerVariant ℕ Bool
GrulerVL = record
  { expressions = Gruler
  ; semantics   = ⟦_⟧ᵍ
  }

⟦ GAsset A  ⟧ᵍ = Leaf-Semantics GrulerVL A
⟦ GPComp PC ⟧ᵍ = ParallelComposition-Semantics GrulerVL PC
⟦ GChoice C ⟧ᵍ = Binary-Choice-Semantics GrulerVL C

gruler-has-leaf : Leaf ∈ Gruler
gruler-has-leaf = record
  { cons = GAsset
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (Leaf A)
        snoc' (GAsset A)  = just A
        snoc' _ = nothing

gruler-has-choice : BinaryChoice ℕ Gruler ∈ Gruler
gruler-has-choice = record
  { cons = GChoice
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (BinaryChoice ℕ Gruler A)
        snoc' (GChoice C) = just C
        snoc' _ = nothing

----- EXAMPLE USAGES OF CONSTRUCTORS -----

make-leaf :
  ∀ (L : 𝕃) → Leaf ∈ L
  → {A : 𝔸} → A
  → L A
make-leaf _ mkLeaf a = cons mkLeaf (leaf a)

make-choice : ∀ {F : 𝔽}
  → (L : 𝕃) → BinaryChoice F L ∈ L
  → {A : 𝔸} → F → L A → L A → L A
make-choice L mkChoice D l r = cons mkChoice (D ⟨ l , r ⟩)

make-gruler-leaf : A → Gruler A
make-gruler-leaf = make-leaf Gruler gruler-has-leaf

make-gruler-choice : ℕ → Gruler A → Gruler A → Gruler A
make-gruler-choice = make-choice Gruler gruler-has-choice

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
