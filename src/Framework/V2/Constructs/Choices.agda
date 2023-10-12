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

module VLChoice₂ where
  open Choice₂ using (_⟨_,_⟩; Config; Standard-Semantics; map; map-preserves)
  open Choice₂.Syntax using (dim)
  open LanguageCompiler using (compile; preserves; conf; fnoc)
  open import Relation.Binary.PropositionalEquality as Eq using (_≗_)

  Syntax : 𝔽 → ℂ
  Syntax F E A = Choice₂.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F Bool (Syntax F)
  Semantics {_} {F} {A} (syn E with-sem ⟦_⟧) choice c = ⟦ Standard-Semantics choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F Bool
  Construct _ F = con Syntax F with-sem Semantics

  -- TODO: - Make the analogous definitions for Choice₂
  --       - Collect this compilation and the preservation proof in a suitable Compiler record.
  compile-language : ∀ {F A} {L₁ L₂ : 𝔼}
    → (L₁ A → L₂ A)
    → Syntax F L₁ A
    → Syntax F L₂ A
  compile-language = map

  Stable : ∀ {F S}
    → (Defs.Config F S → Defs.Config F S)
    → Set
  Stable f = ∀ c → f c ≗ c

  -- TODO: The requirement that also Γ₂ also has to map to Bool makes this proof kind of useless
  --       because we can not translate anything to non-boolean annotations now.
  compile-language-preserves : ∀ {V F} {Γ₁ Γ₂ : VariabilityLanguage V F Bool} {A}
  -- compile-language-preserves : ∀ {V F S} {Γ₁ : VariabilityLanguage V F Bool} {Γ₂ : VariabilityLanguage V F S} {A}
    → (let open IVSet V A using (_≅_; _≅[_][_]_) in
         ∀ (t : LanguageCompiler Γ₁ Γ₂)
         → (chc : Syntax F (Expression Γ₁) A)
         -- TODO: Find proper names and extract these requirements to a proper predicate.
         → Stable (conf t)
         → Stable (fnoc t)
         → Semantics Γ₁ chc ≅[ conf t ][ fnoc t ] Semantics Γ₂ (compile-language {F} {A} {Expression Γ₁} {Expression Γ₂} (compile t) chc))
  compile-language-preserves {V} {F} {Γ₁} {Γ₂} {A} t (D ⟨ l , r ⟩) conf-stable fnoc-stable =
    ≅[]-begin
      Semantics Γ₁ chc
    ≅[]⟨⟩
      (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
    -- First compiler proof composition:
    -- Here, we currently cannot do a simply apply preserves t (which is essentially what we have to do)
    -- but instead we alos have to perform a case analysis because of the nested, twice usage of the index c.
    -- (see proof of t-⊆ for more details)
    ≅[]⟨ t-⊆ , t-⊇ ⟩
      (λ c → ⟦ compile t (Standard-Semantics chc c) ⟧₂ c)
    -- Second compiler proof composition:
    -- We can just apply map-preserves directly.
    -- We need a cong to apply the proof to the first compiler phase instead of the second.
    ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (map-preserves (compile t) chc c) ⟩
      (λ c → ⟦ Standard-Semantics (map (compile t) chc) c ⟧₂ c)
    ≅[]⟨⟩
      (λ c → ⟦ Standard-Semantics (compile-language {F} {A} {Expression Γ₁} {Expression Γ₂} (compile t) chc) c ⟧₂ c)
    ≅[]⟨⟩
      Semantics Γ₂ (compile-language {F} {A} {Expression Γ₁} {Expression Γ₂} (compile t) chc)
    ≅[]-∎
    where module I = IVSet V A
          open I using (_≅[_][_]_; _⊆[_]_)
          open I.≅[]-Reasoning
          open LanguageCompiler using (conf; fnoc)
          open import Data.Bool using (true; false)
          open import Data.Product using (_,_; proj₁; proj₂)

          chc = D ⟨ l , r ⟩
          ⟦_⟧₁ = VariabilityLanguage.Semantics Γ₁
          ⟦_⟧₂ = VariabilityLanguage.Semantics Γ₂

          -- We have to do a manual case distinction here and we cannot chain the proof of preserves without that case distinction.
          -- The problem is that the indices c and z in the indexed sets below are used as an index (second usage, which is fine)
          -- but also within the indexed element (first usage in Standard-Semantics) which is bad.
          -- Such an inner indexing is not supported by indexed sets (yet) so we must eliminate that inner reference,
          -- which we do by case analysis.
          t-⊆ : (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
                ⊆[ conf t ]
                (λ z → ⟦ compile t (Standard-Semantics chc z) ⟧₂ z)
          t-⊆ c rewrite conf-stable c D with c D
          ... | false = proj₁ (preserves t r) c
          ... | true  = proj₁ (preserves t l) c

          t-⊇ : (λ z → ⟦ compile t (Standard-Semantics chc z) ⟧₂ z)
                ⊆[ fnoc t ]
                (λ c → ⟦ Standard-Semantics chc c ⟧₁ c)
          t-⊇ c rewrite fnoc-stable c D with c D
          ... | false = proj₂ (preserves t r) c
          ... | true  = proj₂ (preserves t l) c

module VLChoiceₙ where
  Syntax : 𝔽 → ℂ
  Syntax F E A = Choiceₙ.Syntax F (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} → ℂ-Semantics V F ℕ (Syntax F)
  Semantics {_} {F} {A} (syn E with-sem ⟦_⟧) choice c = ⟦ Choiceₙ.Standard-Semantics choice c ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F ℕ
  Construct _ F = record
    { Construct = Syntax F
    ; _⊢⟦_⟧ = Semantics
    }
