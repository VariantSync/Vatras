open import Framework.Definitions
module Lang.Gruler (F : 𝔽) where

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Framework.Construct
open import Construct.Choices
open import Construct.GrulerArtifacts

open 2Choice using (_⟨_,_⟩)

private
  PC = VLParallelComposition.Syntax
  pc-semantics = PlainConstruct-Semantics VLParallelComposition.Construct VLParallelComposition.ParallelComposition∈ₛGrulerVariant

data Gruler : Size → 𝔼 where
  GAsset  : ∀ {i A} → Leaf (atoms A)                   → Gruler i A
  GPComp  : ∀ {i A} → ParallelComposition (Gruler i A) → Gruler (↑ i) A
  GChoice : ∀ {i A} → VL2Choice.Syntax F (Gruler i) A  → Gruler (↑ i) A

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant (2Choice.Config F) (Gruler i)

GrulerVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
GrulerVL {i} = ⟪ Gruler i , 2Choice.Config F , semantics ⟫

semantics (GAsset a)  _ = VLLeaf.elim-leaf VLLeaf.Leaf∈ₛGrulerVariant a
semantics (GPComp pc)   = pc-semantics GrulerVL pc
semantics (GChoice chc) = VL2Choice.Semantics GrulerVariant F GrulerVL id chc

gruler-has-leaf : ∀ {i} → VLLeaf.Syntax ∈ₛ Gruler i
gruler-has-leaf {i} = record
  { cons = GAsset
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : ∀ {A} → Gruler i A → Maybe (Leaf (atoms A))
        snoc' (GAsset A)  = just A
        snoc' _ = nothing

gruler-has-choice : VL2Choice.Syntax F ∈ₛ Gruler ∞
gruler-has-choice = record
  { cons = GChoice
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : ∀ {i A} → Gruler (↑ i) A → Maybe (VL2Choice.Syntax F (Gruler i) A)
        snoc' (GChoice chc) = just chc
        snoc' _ = nothing

gruler-models-choice : VL2Choice.Construct GrulerVariant F ⟦∈⟧ᵥ GrulerVL
make gruler-models-choice = gruler-has-choice
extract gruler-models-choice = id
preservation gruler-models-choice _ _ = refl

gruler-choice-preserves : ∀ {A : 𝔸} {D l r c}
  → semantics (GChoice {A = A} (D ⟨ l , r ⟩)) c ≡ VL2Choice.Semantics GrulerVariant F GrulerVL id (D ⟨ l , r ⟩) c
gruler-choice-preserves = refl
