{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Constructs.Choices where

open import Data.Bool using (Bool; if_then_else_)
open import Data.String using (String; _<+>_; intersperse)
open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Util.AuxProofs using (if-cong)

module Choice-Fix where
  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ)
  open import Data.Vec using (Vec; lookup; toList) renaming (map to map-vec)
  open import Data.Vec.Properties using (lookup-map)

  record Syntax (n : ℕ) (Q : Set) (A : Set) : Set where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : Vec A n

  Config : ℕ → Set → Set
  Config n Q = Q → Fin n

  -- choice-elimination
  Standard-Semantics : ∀ {n : ℕ} {A : Set} {Q : Set} → Syntax n Q A → Config n Q → A
  Standard-Semantics (D ⟨ alternatives ⟩) c = lookup alternatives (c D)

  map : ∀ {n : ℕ} {Q : Set} {A : Set} {B : Set}
    → (A → B)
    → Syntax n Q A
    → Syntax n Q B
  map f (D ⟨ alternatives ⟩) = D ⟨ map-vec f alternatives ⟩

  -- -- rename
  map-dim : ∀ {n : ℕ} {Q : Set} {R : Set} {A : Set}
    → (Q → R)
    → Syntax n Q A
    → Syntax n R A
  map-dim f (D ⟨ es ⟩) = (f D) ⟨ es ⟩

  map-preserves : ∀ {n : ℕ} {Q : Set} {A : Set} {B : Set}
    → (f : A → B)
    → (chc : Syntax n Q A)
    → (c : Config n Q)
    → Standard-Semantics (map f chc) c ≡ f (Standard-Semantics chc c)
  map-preserves f (D ⟨ es ⟩) c =
    begin
      Standard-Semantics (map f (D ⟨ es ⟩)) c
    ≡⟨⟩
      lookup (map-vec f es) (c D)
    ≡⟨ lookup-map (c D) f es ⟩
      f (lookup es (c D))
    ≡⟨⟩
      f (Standard-Semantics (D ⟨ es ⟩) c)
    ∎

  show : ∀ {n : ℕ} {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax n Q A → String
  show show-q show-a (D ⟨ es ⟩) = show-q D <+> "⟨" <+> (intersperse " , " (toList (map-vec show-a es))) <+> "⟩"

module Choice₂ where
  record Syntax (Q : Set) (A : Set) : Set where
    constructor _⟨_,_⟩
    field
      dim : Q
      l : A
      r : A

  Config : ∀ (Q : Set) → Set
  Config Q = Q → Bool

  -- choice-elimination
  Standard-Semantics : ∀ {A : Set} {Q : Set} → Syntax Q A → Config Q → A
  Standard-Semantics (D ⟨ l , r ⟩) c = if c D then l else r

  map : ∀ {Q : Set} {A : Set} {B : Set}
    → (A → B)
    → Syntax Q A
    → Syntax Q B
  map f (D ⟨ l , r ⟩) = D ⟨ f l , f r ⟩

  -- rename
  map-dim : ∀ {Q : Set} {R : Set} {A : Set}
    → (Q → R)
    → Syntax Q A
    → Syntax R A
  map-dim f (D ⟨ l , r ⟩) = (f D) ⟨ l , r ⟩

  map-preserves : ∀ {Q : Set} {A : Set} {B : Set}
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

  show : ∀ {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax Q A → String
  show show-q show-a (D ⟨ l , r ⟩) = show-q D <+> "⟨" <+> show-a l <+> "," <+> show-a r <+> "⟩"

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺; toList) renaming (map to map-list⁺)
open import Util.List using (find-or-last; map-find-or-last)

module Choiceₙ where
  record Syntax (Q : Set) (A : Set) : Set where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : List⁺ A

  Config : ∀ (Q : Set) → Set
  Config Q = Q → ℕ

  -- choice-elimination
  Standard-Semantics : ∀ {Q : Set} {A : Set} → Syntax Q A → Config Q → A
  Standard-Semantics (D ⟨ alternatives ⟩) c = find-or-last (c D) alternatives

  map : ∀ {Q : Set} {A : Set} {B : Set}
    → (A → B)
    → Syntax Q A
    → Syntax Q B
  map f (dim ⟨ alternatives ⟩) = dim ⟨ map-list⁺ f alternatives ⟩

  -- rename
  map-dim : ∀ {Q : Set} {R : Set} {A : Set}
    → (Q → R)
    → Syntax Q A
    → Syntax R A
  map-dim f (dim ⟨ alternatives ⟩) = (f dim) ⟨ alternatives ⟩

  map-preserves : ∀ {Q : Set} {A : Set} {B : Set}
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

  show : ∀ {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax Q A → String
  show show-q show-a (D ⟨ es ⟩) = show-q D <+> "⟨" <+> (intersperse " , " (toList (map-list⁺ show-a es))) <+> "⟩"

-- Show how choices can be used as constructors in variability languages.
open import Framework.Variant
open import Framework.Definitions
open import Framework.VariabilityLanguage as VL hiding (Config; Semantics)
open import Framework.FunctionLanguage using (to-is-Embedding)
open import Framework.Construct
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (id)

module VLChoice₂ where
  open Choice₂ using (_⟨_,_⟩; Config; Standard-Semantics; map; map-preserves)
  open Choice₂.Syntax using (dim)

  open import Framework.Compiler as Comp using (LanguageCompiler; ConstructFunctor)
  open LanguageCompiler

  Syntax : 𝔽 → ℂ
  Syntax F E A = Choice₂.Syntax F (E A)

  Semantics : ∀ (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (Config F) (Syntax F)
  Semantics _ _ (Lang-⟪ _ , _ , ⟦_⟧ ⟫) extract chc c = ⟦ Standard-Semantics chc (extract c) ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
  Construct V F = Variational-⟪ Syntax F , Config F , Semantics V F ⟫

  map-compile-preserves : ∀ {F V A} → let open IVSet V A using (_≅[_][_]_) in
      ∀ (Γ₁ Γ₂ : VariabilityLanguage V)
      → (extract : Compatible (Construct V F) Γ₁)
      → (t : LanguageCompiler Γ₁ Γ₂)
      → (chc : Syntax F (Expression Γ₁) A)
      → to-is-Embedding (config-compiler t)
      → Semantics V F Γ₁ extract chc
          ≅[ conf t ][ fnoc t ]
        Semantics V F Γ₂ (extract ∘ fnoc t) (map (compile t) chc)
  map-compile-preserves {F} {V} {A} Γ₁ Γ₂ extract t chc stable =
    ≅[]-begin
      Semantics V F Γ₁ extract chc
    ≅[]⟨⟩
      (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
    -- First compiler proof composition:
    -- We apply the hypotheses that t preserves semantics and that its configuration compiler is stable.
    ≅[]⟨ t-⊆ , t-⊇ ⟩
      (λ c → ⟦ compile t (Standard-Semantics chc (extract (fnoc t c))) ⟧₂ c)
    -- Second compiler proof composition:
    -- We can just apply map-preserves directly.
    -- We need a cong to apply the proof to the first compiler phase instead of the second.
    ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (map-preserves (compile t) chc (extract (fnoc t c))) ⟩
      (λ c → ⟦ Standard-Semantics (map (compile t) chc) (extract (fnoc t c)) ⟧₂ c)
    ≅[]⟨⟩
      Semantics V F Γ₂ (extract ∘ fnoc t) (map (compile t) chc)
    ≅[]-∎
    where module I = IVSet V A
          open I using (_≅[_][_]_; _⊆[_]_)
          open I.≅[]-Reasoning

          ⟦_⟧₁ = VL.Semantics Γ₁
          ⟦_⟧₂ = VL.Semantics Γ₂

          t-⊆ : (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
                ⊆[ conf t ]
                (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f)
          t-⊆ i =
            begin
              ⟦ Standard-Semantics chc (extract i) ⟧₁ i
            ≡⟨ proj₁ (preserves t (Standard-Semantics chc (extract i))) i ⟩
              ⟦ compile t (Standard-Semantics chc (extract i)) ⟧₂ (conf t i)
            ≡˘⟨ Eq.cong (λ eq → ⟦ compile t (Standard-Semantics chc (extract eq)) ⟧₂ (conf t i)) (stable i) ⟩
              ⟦ compile t (Standard-Semantics chc (extract (fnoc t (conf t i)))) ⟧₂ (conf t i)
            ≡⟨⟩
              (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f) (conf t i)
            ∎

          t-⊇ : (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f)
                ⊆[ fnoc t ]
                (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
          t-⊇ i =
            begin
              ⟦ compile t (Standard-Semantics chc (extract (fnoc t i))) ⟧₂ i
            ≡⟨ proj₂ (preserves t (Standard-Semantics chc (extract (fnoc t i)))) i ⟩
              ⟦ Standard-Semantics chc (extract (fnoc t i)) ⟧₁ (fnoc t i)
            ≡⟨⟩
              (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c) (fnoc t i)
            ∎

  cong-compiler : ∀ V F → ConstructFunctor (Construct V F)
  cong-compiler _ _ = record
    { map = map
    ; preserves = map-compile-preserves
    }

module VLChoiceₙ where
  open Choiceₙ using (_⟨_⟩; Config; Standard-Semantics; map; map-preserves)
  open Choiceₙ.Syntax using (dim)

  open import Framework.Compiler as Comp using (LanguageCompiler; ConstructFunctor)
  open LanguageCompiler

  Syntax : 𝔽 → ℂ
  Syntax F E A = Choiceₙ.Syntax F (E A)

  Semantics : ∀ (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (Config F) (Syntax F)
  Semantics _ _ (Lang-⟪ _ , _ , ⟦_⟧ ⟫) extract choice c = ⟦ Choiceₙ.Standard-Semantics choice (extract c) ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
  Construct V F = Variational-⟪ Syntax F , Config F , Semantics V F ⟫

  -- Interestingly, this proof is entirely copy and paste from VLChoice₂.map-compile-preserves.
  -- Only minor adjustments to adapt the theorem had to be made.
  -- Is there something useful to extract to a common definition here?
  -- This proof is oblivious of at least
  --   - the implementation of map, we only need the preservation theorem
  --   - the Standard-Semantics, we only need the preservation theorem of t, and that the config-compiler is stable.
  map-compile-preserves : ∀ {F V A} → let open IVSet V A using (_≅[_][_]_) in
      ∀ (Γ₁ Γ₂ : VariabilityLanguage V)
      → (extract : Compatible (Construct V F) Γ₁)
      → (t : LanguageCompiler Γ₁ Γ₂)
      → (chc : Syntax F (Expression Γ₁) A)
      → to-is-Embedding (config-compiler t)
      → Semantics V F Γ₁ extract chc
          ≅[ conf t ][ fnoc t ]
        Semantics V F Γ₂ (extract ∘ fnoc t) (map (compile t) chc)
  map-compile-preserves {F} {V} {A} Γ₁ Γ₂ extract t chc stable =
    ≅[]-begin
      Semantics V F Γ₁ extract chc
    ≅[]⟨⟩
      (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
    -- First compiler proof composition:
    -- We apply the hypotheses that t preserves semantics and that its configuration compiler is stable.
    ≅[]⟨ t-⊆ , t-⊇ ⟩
      (λ c → ⟦ compile t (Standard-Semantics chc (extract (fnoc t c))) ⟧₂ c)
    -- Second compiler proof composition:
    -- We can just apply map-preserves directly.
    -- We need a cong to apply the proof to the first compiler phase instead of the second.
    ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (map-preserves (compile t) chc (extract (fnoc t c))) ⟩
      (λ c → ⟦ Standard-Semantics (map (compile t) chc) (extract (fnoc t c)) ⟧₂ c)
    ≅[]⟨⟩
      Semantics V F Γ₂ (extract ∘ fnoc t) (map (compile t) chc)
    ≅[]-∎
    where module I = IVSet V A
          open I using (_≅[_][_]_; _⊆[_]_)
          open I.≅[]-Reasoning

          ⟦_⟧₁ = VL.Semantics Γ₁
          ⟦_⟧₂ = VL.Semantics Γ₂

          t-⊆ : (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
                ⊆[ conf t ]
                (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f)
          t-⊆ i =
            begin
              ⟦ Standard-Semantics chc (extract i) ⟧₁ i
            ≡⟨ proj₁ (preserves t (Standard-Semantics chc (extract i))) i ⟩
              ⟦ compile t (Standard-Semantics chc (extract i)) ⟧₂ (conf t i)
            ≡˘⟨ Eq.cong (λ eq → ⟦ compile t (Standard-Semantics chc (extract eq)) ⟧₂ (conf t i)) (stable i) ⟩
              ⟦ compile t (Standard-Semantics chc (extract (fnoc t (conf t i)))) ⟧₂ (conf t i)
            ≡⟨⟩
              (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f) (conf t i)
            ∎

          t-⊇ : (λ f → ⟦ compile t (Standard-Semantics chc (extract (fnoc t f))) ⟧₂ f)
                ⊆[ fnoc t ]
                (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c)
          t-⊇ i =
            begin
              ⟦ compile t (Standard-Semantics chc (extract (fnoc t i))) ⟧₂ i
            ≡⟨ proj₂ (preserves t (Standard-Semantics chc (extract (fnoc t i)))) i ⟩
              ⟦ Standard-Semantics chc (extract (fnoc t i)) ⟧₁ (fnoc t i)
            ≡⟨⟩
              (λ c → ⟦ Standard-Semantics chc (extract c) ⟧₁ c) (fnoc t i)
            ∎

  cong-compiler : ∀ V F → ConstructFunctor (Construct V F)
  cong-compiler _ _ = record
    { map = map
    ; preserves = map-compile-preserves
    }
