{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Constructs.Choices where

open import Data.Bool using (Bool; if_then_else_)
open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Util.AuxProofs using (if-cong)

module Choice₂ where
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
    → (c : Config Q) -- todo: use ≐ here?
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
open import Framework.V2.Definitions as Defs hiding (Semantics; Config)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (id)

module VLChoice₂ where
  open Choice₂ using (_⟨_,_⟩; Config; Standard-Semantics; map; map-preserves)
  open Choice₂.Syntax using (dim)

  open import Framework.V2.Compiler as Comp using (LanguageCompiler; ConfigTranslation; ConstructFunctor; Stable)
  open LanguageCompiler

  Syntax : ℂ
  Syntax F E A = Choice₂.Syntax F (E A)

  Semantics : ∀ (F : 𝔽) → ℂ-Semantics F Bool Syntax
  Semantics _ (syn _ with-sem ⟦_⟧) fnoc chc c = ⟦ Standard-Semantics chc (fnoc c) ⟧ c

  Construct : ∀ (F : 𝔽) → VariabilityConstruct F Bool
  Construct F = con Syntax with-sem Semantics F

  -- TODO: Make the analogous definitions for Choice₂
  map-compile-preserves : ∀ {V} {F₁ F₂ : 𝔽} {S₂ : 𝕊} {Γ₁ : VariabilityLanguage V F₁ Bool} {Γ₂ : VariabilityLanguage V F₂ S₂} {A}
    → let open Comp.IVSet V A using (_≅_; _≅[_][_]_) in
    ∀ (t : LanguageCompiler Γ₁ Γ₂)
    → (chc : Syntax F₁ (Expression Γ₁) A)
    → Stable (config-compiler t)
    → Semantics F₁ Γ₁ id chc
        ≅[ conf t ][ fnoc t ]
      Semantics F₁ Γ₂ (fnoc t) (map (compile t) chc)
  map-compile-preserves {V} {F₁} {_} {_} {Γ₁} {Γ₂} {A} t chc stable =
    ≅[]-begin
      Semantics F₁ Γ₁ id chc
    ≅[]⟨⟩
      (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
    -- First compiler proof composition:
    -- We apply the hypotheses that t preserves semantics and that its configuration compiler is stable.
    ≅[]⟨ t-⊆ , t-⊇ ⟩
      (λ c → ⟦ compile t (Standard-Semantics chc (fnoc t c)) ⟧₂ c)
    -- Second compiler proof composition:
    -- We can just apply map-preserves directly.
    -- We need a cong to apply the proof to the first compiler phase instead of the second.
    ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (map-preserves (compile t) chc (fnoc t c)) ⟩
      (λ c → ⟦ Standard-Semantics (map (compile t) chc) (fnoc t c) ⟧₂ c)
    ≅[]⟨⟩
      Semantics F₁ Γ₂ (fnoc t) (map (compile t) chc)
    ≅[]-∎
    where module I = Comp.IVSet V A
          open I using (_≅[_][_]_; _⊆[_]_)
          open I.≅[]-Reasoning

          ⟦_⟧₁ = VariabilityLanguage.Semantics Γ₁
          ⟦_⟧₂ = VariabilityLanguage.Semantics Γ₂

          t-⊆ : (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
                ⊆[ conf t ]
                (λ f → ⟦ compile t (Standard-Semantics chc (fnoc t f)) ⟧₂ f)
          t-⊆ i =
            begin
              ⟦ Standard-Semantics chc i ⟧₁ i
            ≡⟨ proj₁ (preserves t (Standard-Semantics chc i)) i ⟩
              ⟦ compile t (Standard-Semantics chc i) ⟧₂ (conf t i)
            ≡˘⟨ Eq.cong (λ eq → ⟦ compile t (Standard-Semantics chc eq) ⟧₂ (conf t i)) (stable i) ⟩
              ⟦ compile t (Standard-Semantics chc (fnoc t (conf t i))) ⟧₂ (conf t i)
            ≡⟨⟩
              (λ f → ⟦ compile t (Standard-Semantics chc (fnoc t f)) ⟧₂ f) (conf t i)
            ∎

          t-⊇ : (λ f → ⟦ compile t (Standard-Semantics chc (fnoc t f)) ⟧₂ f)
                ⊆[ fnoc t ]
                (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
          t-⊇ i =
            begin
              ⟦ compile t (Standard-Semantics chc (fnoc t i)) ⟧₂ i
            ≡⟨ proj₂ (preserves t (Standard-Semantics chc (fnoc t i))) i ⟩
              ⟦ Standard-Semantics chc (fnoc t i) ⟧₁ (fnoc t i)
            ≡⟨⟩
              (λ c → ⟦ Standard-Semantics chc c ⟧₁ c) (fnoc t i)
            ∎

  cong-compiler : ∀ F → ConstructFunctor (Construct F)
  cong-compiler _ = record
    { map = map
    ; preserves = map-compile-preserves
    }

module VLChoiceₙ where
  Syntax : ℂ
  Syntax F E A = Choiceₙ.Syntax F (E A)

  Semantics : ∀ {F : 𝔽} → ℂ-Semantics F ℕ Syntax
  Semantics {_} {F} {A} (syn E with-sem ⟦_⟧) fnoc choice c = ⟦ Choiceₙ.Standard-Semantics choice (fnoc c) ⟧ c

  Construct : ∀ (F : 𝔽) → VariabilityConstruct F ℕ
  Construct _ = record
    { Construct = Syntax
    ; construct-semantics = Semantics
    }
