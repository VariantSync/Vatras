{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.Gruler (F : 𝔽) where

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Constructs.Choices
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Variants using (GrulerVariant)

open Framework.V2.Constructs.Choices.Choice₂ using (_⟨_,_⟩)

private
  PC = VLParallelComposition.Syntax
  pc-semantics = VLParallelComposition.Semantics
  Choice₂ = VLChoice₂.Syntax
  choice₂-semantics = VLChoice₂.Semantics

data Gruler : Size → 𝔼 where
  GAsset  : ∀ {i A} → Leaf A                           → Gruler i A
  GPComp  : ∀ {i A} → ParallelComposition (Gruler i A) → Gruler (↑ i) A
  GChoice : ∀ {i A} → Choice₂ F (Gruler i) A      → Gruler (↑ i) A

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant F Bool (Gruler i)

GrulerVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant F Bool
GrulerVL {i} = syn Gruler i with-sem semantics

semantics (GAsset a)  _ = VLLeaf.elim-leaf F VLLeaf.Leaf∈ₛGrulerVariant a
semantics (GPComp pc)   = pc-semantics VLParallelComposition.ParallelComposition∈ₛGrulerVariant id GrulerVL pc
semantics (GChoice chc) = choice₂-semantics GrulerVariant F id (GrulerVL) chc

gruler-has-leaf : ∀ {i} → F ⊢ VLLeaf.Syntax ∈ₛ Gruler i
gruler-has-leaf {i} = record
  { cons = GAsset
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : ∀ {A} → Gruler i A → Maybe (Leaf A)
        snoc' (GAsset A)  = just A
        snoc' _ = nothing

gruler-has-choice : F ⊢ Choice₂ ∈ₛ Gruler ∞
gruler-has-choice = record
  { cons = GChoice
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : ∀ {i A} → Gruler (↑ i) A → Maybe (Choice₂ F (Gruler i) A)
        snoc' (GChoice chc) = just chc
        snoc' _ = nothing

gruler-models-choice : VLChoice₂.Construct GrulerVariant F ⟦∈⟧ GrulerVL
make gruler-models-choice = gruler-has-choice
preservation gruler-models-choice _ _ = refl

gruler-choice-preserves : ∀ {A : 𝔸} {D l r c}
  → semantics (GChoice {A = A} (D ⟨ l , r ⟩)) c ≡ choice₂-semantics GrulerVariant F id GrulerVL (D ⟨ l , r ⟩) c
gruler-choice-preserves = refl
