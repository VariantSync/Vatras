module Framework.V2.Constructs.Choices where

open import Data.Bool using (Bool; if_then_else_)
open import Level using (Level; _⊔_)

module Choice₂ {ℓ₁ : Level} (Q : Set ℓ₁) where
  record Syntax {ℓ₂ : Level} (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _⟨_,_⟩
    field
      dim : Q
      l : A
      r : A

  Config : Set ℓ₁
  Config = Q → Bool

  Standard-Semantics : ∀ {ℓ₂} {A : Set ℓ₂} → Syntax A → Config → A
  Standard-Semantics (D ⟨ l , r ⟩) c = if c D then l else r

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺)
open import Util.List using (find-or-last)

module Choiceₙ {ℓ₁ : Level} (Q : Set ℓ₁) where
  record Syntax {ℓ₂ : Level} (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : List⁺ A

  Config : Set ℓ₁
  Config = Q → ℕ

  Standard-Semantics : ∀ {ℓ₂} {A : Set ℓ₂} → Syntax A → Config → A
  Standard-Semantics (D ⟨ alternatives ⟩) c = find-or-last (c D) alternatives

open import Data.List using ([]; _∷_)
open Data.List.NonEmpty using (_∷_)

module _ where
  open Choice₂ using (_⟨_,_⟩)
  open Choiceₙ using (_⟨_⟩)

  2→N : ∀ {ℓ₁ ℓ₂} {D : Set ℓ₁} {A : Set ℓ₂} → Choice₂.Syntax D A → Choiceₙ.Syntax D A
  2→N (D ⟨ l , r ⟩) = D ⟨ l ∷ r ∷ [] ⟩

-- Show how choices can be used as constructors in variability languages.
open import Framework.V2.Definitions

module VLChoice₂ where
  Syntax : 𝔽 → ℂ
  Syntax F E A = Choice₂.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F Bool (Syntax F)
  Semantics {_} {F} {A} (E with-sem ⟦_⟧) choice c = ⟦ Choice₂.Standard-Semantics F choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F Bool
  Construct _ F = record
    { construct = Syntax F
    ; semantics = Semantics
    }

module VLChoiceₙ where
  Syntax : 𝔽 → ℂ
  Syntax F E A = Choiceₙ.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F ℕ (Syntax F)
  Semantics {_} {F} {A} (E with-sem ⟦_⟧) choice c = ⟦ Choiceₙ.Standard-Semantics F choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F ℕ
  Construct _ F = record
    { construct = Syntax F
    ; semantics = Semantics
    }
