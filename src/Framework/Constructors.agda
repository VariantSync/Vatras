{-# OPTIONS --sized-types #-}
module Framework.Constructors where

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

-- configuration languages
ℂ : Set₁
ℂ = Set

-- an annotation language
𝕃 : Set₁
𝕃 = 𝔸 → Set

-- constructor arguments
CArg : Set₁
CArg = 𝕃 → 𝔸 → Set

-- constructors (or grammar rules) for annotation langauges
Constructor : CArg → 𝕃 → Set₁
Constructor P L = ∀ {A : 𝔸} → P L A → L A

record Artifact (L : 𝕃) (A : 𝔸) : Set where
  constructor _-<_>-
  field
    value : A
    children : List (L A)

record BinaryChoice (L : 𝕃) (A : 𝔸) : Set where
  constructor _⟨_,_⟩
  field
    name : Name
    l : L A
    r : L A

record Choice (L : 𝕃) (A : 𝔸) : Set where
  constructor _⟨_⟩
  field
    name : Name
    alternatives : List⁺ (L A)

record Option (L : 𝕃) (A : 𝔸) : Set where
  constructor _〔_〕
  field
    name : Name
    child : L A

data Variant : 𝕃 where
  Artifactᵥ : ∀ {A : 𝔸} → Artifact Variant A → Variant A

data CC₂ : 𝕃 where
  Artifact₂ : ∀ {A : 𝔸} → Artifact CC₂ A → CC₂ A
  Choice₂ : ∀ {A : 𝔸} → BinaryChoice CC₂ A → CC₂ A

data CCₙ : 𝕃 where
  Artifactₙ : ∀ {A : 𝔸} → Artifact CCₙ A → CCₙ A
  Choiceₙ : ∀ {A : 𝔸} → Choice CCₙ A → CCₙ A

data OC : 𝕃 where
  Artifactₒ : ∀ {A : 𝔸} → Artifact OC A → OC A
  Optionₒ : ∀ {A : 𝔸} → Option OC A → OC A

Semantics : ℂ → 𝕃 → Set₁
Semantics C L = ∀ {A : 𝔸} → L A → C → Variant A

VariantSetoid : 𝔸 → Setoid 0ℓ 0ℓ
VariantSetoid A = Eq.setoid (Variant A)

IndexedVMap : 𝔸 → Set → Set
IndexedVMap A I = IndexedSet I
  where open Data.IndexedSet (VariantSetoid A) using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : 𝔸 → ℕ → Set
VMap A n = IndexedVMap A (Fin (suc n))

Complete : (C : ℂ) → (L : 𝕃) → Semantics C L → Set₁
Complete C L ⟦_⟧ = ∀ {A n}
  → (vs : VMap A n)
    ----------------------------------
  → Σ[ e ∈ L A ]
      (let open Data.IndexedSet (VariantSetoid A) using (_≅_)
        in vs ≅ ⟦ e ⟧)

-- any language with artifacts and choices is complete
choices-make-complete :
  ∀ (C : ℂ) (L : 𝕃) (S : Semantics C L)
  → Constructor Artifact L
  → Constructor Choice L
  → Complete C L S
-- TODO: Reuse the proof that variant lists are complete. Then show that
--       every language with at least artifacts and choices is at least
--       as expressive as a variant list.
choices-make-complete C L ⟦_⟧ mkArtifact mkChoice vs = {!!}

binary-to-nary-choice :
  ∀ {L₁ L₂ A}
  → (translation : L₁ A → L₂ A)
  → BinaryChoice L₁ A
  → Choice L₂ A
binary-to-nary-choice t (D ⟨ l , r ⟩) = D ⟨ t l ∷ t r ∷ [] ⟩

artifact-translation :
  ∀ {L₁ L₂ A}
  → (translation : L₁ A → L₂ A)
  → Artifact L₁ A
  → Artifact L₂ A
artifact-translation t (a -< es >-) = a -< map t es >-

module _ {A : 𝔸} where
  open import Data.List.Relation.Unary.All using (All)
  open Data.IndexedSet (VariantSetoid A) using (_≅_)
  open Data.Product using (_,_)

  artifact-translation-preserves :
    ∀ {L₁ L₂ : 𝕃}
    → {C₁ C₂ : ℂ}
    → {⟦_⟧₁ : Semantics C₁ L₁}
    → {⟦_⟧₂ : Semantics C₂ L₂}
    → (mkArtifact₁ : Constructor Artifact L₁)
    → (mkArtifact₂ : Constructor Artifact L₂)
    → (t : L₁ A → L₂ A)
    → (a : A)
    → (es : List (L₁ A))
    → (All (λ e → ⟦ e ⟧₁ ≅ ⟦ t e ⟧₂) es)
    → ⟦ mkArtifact₁ (a -< es >-) ⟧₁ ≅ ⟦ mkArtifact₂ (artifact-translation {L₁} {L₂} t (a -< es >-)) ⟧₂
  artifact-translation-preserves mkArtifact₁ mkArtifact₂ t a es t-preserves-es = {!!}
  -- Proving this is actually quite hard. We again need the traversable over configurations somehow.
  -- Instead of continuing to prove this, we should try to use it:
  -- What would be the benfit of having this proof?
  -- Would it really avoid duplication and would it help us for proofs of expressiveness?
  -- Also proving the preservation of binary-to-nary-choice might be easier.

{-# TERMINATING #-}
CC₂→CCₙ : ∀ {A} → CC₂ A → CCₙ A
CC₂→CCₙ (Artifact₂ a) = Artifactₙ (artifact-translation CC₂→CCₙ a)
CC₂→CCₙ (Choice₂ c) = Choiceₙ (binary-to-nary-choice CC₂→CCₙ c)

-- Examples on how to use constructors to make functions that abstract over languages.
leaf :
  ∀ {L : 𝕃} → Constructor Artifact L
  → {A : 𝔸} → (a : A)
  → L A
leaf mkArtifact a = mkArtifact (a -< [] >-)

variant-leaf : ∀ {A : 𝔸} (a : A) → Variant A
variant-leaf = leaf Artifactᵥ

cc₂-leaf : ∀ {A : 𝔸} (a : A) → CC₂ A
cc₂-leaf = leaf Artifact₂
