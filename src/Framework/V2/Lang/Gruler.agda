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

semantics : ∀ {i : Size} → (R : (F → Bool) → Set) → 𝔼-Semantics GrulerVariant F Bool R (Gruler i)

GrulerVL : ∀ {i : Size} → (R : (F → Bool) → Set) → VariabilityLanguage GrulerVariant F Bool R
GrulerVL {i} R = syn Gruler i with-sem semantics R

semantics R (GAsset a)  _ = VLLeaf.elim-leaf F VLLeaf.Leaf∈ₛGrulerVariant a
semantics R (GPComp pc)   = pc-semantics VLParallelComposition.ParallelComposition∈ₛGrulerVariant id (GrulerVL R) pc
semantics R (GChoice chc) = choice₂-semantics GrulerVariant F R id (GrulerVL R) chc

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

gruler-models-choice :  (R : (F → Bool) → Set) → VLChoice₂.Construct GrulerVariant F R ⟦∈⟧ (GrulerVL R)
gruler-models-choice R .make = gruler-has-choice
gruler-models-choice R .preservation _ _ = refl

gruler-choice-preserves : ∀ {A : 𝔸} {R} {D l r c}
  → semantics R (GChoice {A = A} (D ⟨ l , r ⟩)) c ≡ choice₂-semantics GrulerVariant F R id (GrulerVL R) (D ⟨ l , r ⟩) c
gruler-choice-preserves = refl
