module Framework.V2.Constructs.Choices where

open import Data.Bool using (Bool; if_then_else_)
open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Util.AuxProofs using (if-cong)

module Choice₂  where
  record Syntax {ℓ₁ ℓ₂ : Level} (Q : Set ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _⟨_,_⟩
    field
      dim : Q
      l : A
      r : A

  Config : ∀ {ℓ₁} (Q : Set ℓ₁) → Set ℓ₁
  Config Q = Q → Bool

  -- choice-elimination
  Standard-Semantics : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₂} {Q : Set ℓ₁} → Syntax Q A → Config Q → A
  Standard-Semantics (D ⟨ l , r ⟩) c = if c D then l else r

  map : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
    → (A → B)
    → Syntax Q A
    → Syntax Q B
  map f (D ⟨ l , r ⟩) = D ⟨ f l , f r ⟩

  -- rename
  map-dim : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {R : Set ℓ₂} {A : Set ℓ₃}
    → (Q → R)
    → Syntax Q A
    → Syntax R A
  map-dim f (D ⟨ l , r ⟩) = (f D) ⟨ l , r ⟩

  map-preserves : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
    → (f : A → B)
    → (chc : Syntax Q A)
    → (c : Config Q)
    → Standard-Semantics (map f chc) c ≡ f (Standard-Semantics chc c)
  map-preserves f (D ⟨ l , r ⟩) c =
    begin
      Standard-Semantics (map f (D ⟨ l , r ⟩)) c
    ≡⟨⟩
      (if c D then f l else f r)
    ≡⟨ if-cong (c D) f ⟩
      f (if c D then l else r)
    ≡⟨⟩
      f (Standard-Semantics (D ⟨ l , r ⟩) c)
    ∎

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺) renaming (map to map-list⁺)
open import Util.List using (find-or-last; map-find-or-last)

module Choiceₙ where
  record Syntax {ℓ₁ ℓ₂ : Level} (Q : Set ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : List⁺ A

  Config : ∀ {ℓ₁} (Q : Set ℓ₁) → Set ℓ₁
  Config Q = Q → ℕ

  -- choice-elimination
  Standard-Semantics : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Syntax Q A → Config Q → A
  Standard-Semantics (D ⟨ alternatives ⟩) c = find-or-last (c D) alternatives

  map : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
    → (A → B)
    → Syntax Q A
    → Syntax Q B
  map f (dim ⟨ alternatives ⟩) = dim ⟨ map-list⁺ f alternatives ⟩

  -- rename
  map-dim : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {R : Set ℓ₂} {A : Set ℓ₃}
    → (Q → R)
    → Syntax Q A
    → Syntax R A
  map-dim f (dim ⟨ alternatives ⟩) = (f dim) ⟨ alternatives ⟩

  map-preserves : ∀ {ℓ₁ ℓ₂ ℓ₃} {Q : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
    → (f : A → B)
    → (chc : Syntax Q A)
    → (c : Config Q)
    → Standard-Semantics (map f chc) c ≡ f (Standard-Semantics chc c)
  map-preserves f (D ⟨ as ⟩) c =
    begin
      Standard-Semantics (map f (D ⟨ as ⟩)) c
    ≡⟨⟩
      find-or-last (c D) (map-list⁺ f as)
    ≡˘⟨ map-find-or-last f (c D) as ⟩
      f (find-or-last (c D) as)
    ≡⟨⟩
      f (Standard-Semantics (D ⟨ as ⟩) c)
    ∎

-- Show how choices can be used as constructors in variability languages.
open import Framework.V2.Definitions hiding (Semantics)

module VLChoice₂ where
  Syntax : 𝔽 → ℂ
  Syntax F E A = Choice₂.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F Bool (Syntax F)
  Semantics {_} {F} {A} (E with-sem ⟦_⟧) choice c = ⟦ Choice₂.Standard-Semantics choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F Bool
  Construct _ F = record
    { Construct = Syntax F
    ; _⊢⟦_⟧ = Semantics
    }

module VLChoiceₙ where
  Syntax : 𝔽 → ℂ
  Syntax F E A = Choiceₙ.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F ℕ (Syntax F)
  Semantics {_} {F} {A} (E with-sem ⟦_⟧) choice c = ⟦ Choiceₙ.Standard-Semantics choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F ℕ
  Construct _ F = record
    { Construct = Syntax F
    ; _⊢⟦_⟧ = Semantics
    }
