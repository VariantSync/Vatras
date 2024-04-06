{-# OPTIONS --allow-unsolved-metas #-}
module Construct.Choices where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Bool.Properties using (push-function-into-if)
open import Data.String using (String; _<+>_; intersperse)
open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.EqIndexedSet as ISet

module NChoice where
  open import Data.Fin using (Fin)
  open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥)
  open import Data.Vec using (Vec; lookup; toList) renaming (map to map-vec)
  open import Data.Vec.Properties using (lookup-map)

  record Syntax (n : ℕ≥ 2) (Q : Set) (A : Set) : Set where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : Vec A (ℕ≥.toℕ n)

  Config : ℕ≥ 2 → Set → Set
  Config n Q = Q → Fin (ℕ≥.toℕ n)

  -- choice-elimination
  ⟦_⟧ : ∀ {n : ℕ≥ 2} {A : Set} {Q : Set} → Syntax n Q A → Config n Q → A
  ⟦_⟧ (D ⟨ alternatives ⟩) c = lookup alternatives (c D)

  map : ∀ {n : ℕ≥ 2} {Q : Set} {A : Set} {B : Set}
    → (A → B)
    → Syntax n Q A
    → Syntax n Q B
  map f (D ⟨ alternatives ⟩) = D ⟨ map-vec f alternatives ⟩

  -- -- rename
  map-dim : ∀ {n : ℕ≥ 2} {Q : Set} {R : Set} {A : Set}
    → (Q → R)
    → Syntax n Q A
    → Syntax n R A
  map-dim f (D ⟨ es ⟩) = (f D) ⟨ es ⟩

  map-preserves : ∀ {n : ℕ≥ 2} {Q : Set} {A : Set} {B : Set}
    → (f : A → B)
    → (chc : Syntax n Q A)
    → (c : Config n Q)
    → ⟦ map f chc ⟧ c ≡ f (⟦ chc ⟧ c)
  map-preserves {n} f (D ⟨ es ⟩) c =
    begin
      ⟦ map {n} f (D ⟨ es ⟩) ⟧ c
    ≡⟨⟩
      lookup (map-vec f es) (c D)
    ≡⟨ lookup-map (c D) f es ⟩
      f (lookup es (c D))
    ≡⟨⟩
      f (⟦_⟧ {n} (D ⟨ es ⟩) c) -- TODO implicit argument
    ∎

  show : ∀ {n : ℕ≥ 2} {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax n Q A → String
  show show-q show-a (D ⟨ es ⟩) = show-q D <+> "⟨" <+> (intersperse " , " (toList (map-vec show-a es))) <+> "⟩"

module 2Choice where
  record Syntax (Q : Set) (A : Set) : Set where
    constructor _⟨_,_⟩
    field
      dim : Q
      l : A
      r : A

  Config : ∀ (Q : Set) → Set
  Config Q = Q → Bool

  -- choice-elimination
  ⟦_⟧ : ∀ {A : Set} {Q : Set} → Syntax Q A → Config Q → A
  ⟦_⟧ (D ⟨ l , r ⟩) c = if c D then l else r

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
    → ⟦ map f chc ⟧ c ≡ f (⟦ chc ⟧ c)
  map-preserves f (D ⟨ l , r ⟩) c =
    begin
      ⟦ map f (D ⟨ l , r ⟩) ⟧ c
    ≡⟨⟩
      (if c D then f l else f r)
    ≡˘⟨ push-function-into-if f (c D) ⟩
      f (if c D then l else r)
    ≡⟨⟩
      f (⟦ D ⟨ l , r ⟩ ⟧ c)
    ∎

  show : ∀ {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax Q A → String
  show show-q show-a (D ⟨ l , r ⟩) = show-q D <+> "⟨" <+> show-a l <+> "," <+> show-a r <+> "⟩"

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺; toList) renaming (map to map-list⁺)
open import Util.List using (find-or-last; map-find-or-last)

module Choice where
  record Syntax (Q : Set) (A : Set) : Set where
    constructor _⟨_⟩
    field
      dim : Q
      alternatives : List⁺ A

  Config : ∀ (Q : Set) → Set
  Config Q = Q → ℕ

  -- choice-elimination
  ⟦_⟧ : ∀ {Q : Set} {A : Set} → Syntax Q A → Config Q → A
  ⟦_⟧ (D ⟨ alternatives ⟩) c = find-or-last (c D) alternatives

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
    → ⟦ map f chc ⟧ c ≡ f (⟦ chc ⟧ c)
  map-preserves f (D ⟨ as ⟩) c =
    begin
      ⟦ map f (D ⟨ as ⟩) ⟧ c
    ≡⟨⟩
      find-or-last (c D) (map-list⁺ f as)
    ≡˘⟨ map-find-or-last f (c D) as ⟩
      f (find-or-last (c D) as)
    ≡⟨⟩
      f (⟦ D ⟨ as ⟩ ⟧ c)
    ∎

  show : ∀ {Q : Set} {A : Set} → (Q → String) → (A → String) → Syntax Q A → String
  show show-q show-a (D ⟨ es ⟩) = show-q D <+> "⟨" <+> (intersperse " , " (toList (map-list⁺ show-a es))) <+> "⟩"

-- Show how choices can be used as constructors in variability languages.
open import Framework.Definitions
open import Framework.VariabilityLanguage as VL hiding (Config; Semantics)
open import Framework.Relation.Function using (to-is-Embedding)
open import Framework.Construct
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (id)

module VLNChoice where
  open import Util.Nat.AtLeast using (ℕ≥)
  open NChoice using (Config; map; map-preserves)
  open NChoice.Syntax using (dim)

  Syntax : ℕ≥ 2 → 𝔽 → ℂ
  Syntax n F E A = NChoice.Syntax n F (E A)

  Semantics : ∀ (n : ℕ≥ 2) (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (Config n F) (Syntax n F)
  Semantics _ _ _ (⟪ _ , _ , ⟦_⟧ ⟫) extract chc c = ⟦ NChoice.⟦ chc ⟧ (extract c) ⟧ c

  Construct : ∀ n (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
  Construct n V F = Variational-⟪ Syntax n F , Config n F , Semantics n V F ⟫

module VL2Choice where
  open 2Choice using (_⟨_,_⟩; Config; map; map-preserves)
  open 2Choice.Syntax using (dim)

  Syntax : 𝔽 → ℂ
  Syntax F E A = 2Choice.Syntax F (E A)

  Semantics : ∀ (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (Config F) (Syntax F)
  Semantics _ _ (⟪ _ , _ , ⟦_⟧ ⟫) extract chc c = ⟦ 2Choice.⟦ chc ⟧ (extract c) ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
  Construct V F = Variational-⟪ Syntax F , Config F , Semantics V F ⟫

module VLChoice where
  open Choice using (_⟨_⟩; Config; map; map-preserves)
  open Choice.Syntax using (dim)

  Syntax : 𝔽 → ℂ
  Syntax F E A = Choice.Syntax F (E A)

  Semantics : ∀ (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (Config F) (Syntax F)
  Semantics _ _ (⟪ _ , _ , ⟦_⟧ ⟫) extract choice c = ⟦ Choice.⟦ choice ⟧ (extract c) ⟧ c

  Construct : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
  Construct V F = Variational-⟪ Syntax F , Config F , Semantics V F ⟫
