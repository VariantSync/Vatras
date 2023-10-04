module Framework.V2.Lang.Gruler where

open import Framework.V2.Definitions

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Constructs.Choices
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Variants using (GrulerVariant)

open Framework.V2.Constructs.Choices.Choice₂ using (_⟨_,_⟩)

private
  variable
    A : 𝔸

  BinaryChoice = VLChoice₂.Syntax
  BinaryChoice-Semantics = VLChoice₂.Semantics

data Gruler : 𝔼 where
  GAsset  : Leaf A                       → Gruler A
  GPComp  : ParallelComposition (Gruler A) → Gruler A
  GChoice : BinaryChoice ℕ Gruler A      → Gruler A

-- I have no idea how we could prove this terminating but let's just avoid that headache.
{-# TERMINATING #-}
⟦_⟧ᵍ : 𝔼-Semantics GrulerVariant ℕ Bool Gruler

GrulerVL : VariabilityLanguage GrulerVariant ℕ Bool
GrulerVL = record
  { expression-set = Gruler
  ; semantics   = ⟦_⟧ᵍ
  }

⟦ GAsset A  ⟧ᵍ = VLLeaf.Semantics VLLeaf.Leaf∈ₛGrulerVariant GrulerVL A
⟦ GPComp PC ⟧ᵍ = VLParallelComposition.Semantics VLParallelComposition.ParallelComposition∈ₛGrulerVariant GrulerVL PC
⟦ GChoice C ⟧ᵍ = BinaryChoice-Semantics GrulerVL C

gruler-has-leaf : VLLeaf.Syntax ∈ₛ Gruler
gruler-has-leaf = record
  { cons = GAsset
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (Leaf A)
        snoc' (GAsset A)  = just A
        snoc' _ = nothing

gruler-has-choice : BinaryChoice ℕ ∈ₛ Gruler
gruler-has-choice = record
  { cons = GChoice
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (BinaryChoice ℕ Gruler A)
        snoc' (GChoice C) = just C
        snoc' _ = nothing

gruler-models-choice : VLChoice₂.Construct GrulerVariant ℕ ⟦∈⟧ GrulerVL
make gruler-models-choice = gruler-has-choice
preservation gruler-models-choice _ _ = refl

gruler-choice-preserves : ∀ {D l r c}
  → ⟦ GChoice {A} (D ⟨ l , r ⟩) ⟧ᵍ c ≡ BinaryChoice-Semantics GrulerVL (D ⟨ l , r ⟩) c
gruler-choice-preserves = refl
