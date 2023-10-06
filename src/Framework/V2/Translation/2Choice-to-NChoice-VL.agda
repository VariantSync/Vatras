open import Framework.V2.Definitions

module Framework.V2.Translation.2Choice-to-NChoice-VL {F : 𝔽} where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Function using (_∘_)

-- open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

import Framework.V2.Translation.2Choice-to-NChoice as 2→N
open 2→N using (ConfSpec; FnocSpec)

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂; map to map₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Config to Configₙ; map to mapₙ)

module Translate {F : 𝔽} {V : 𝕍} {A : 𝔸}
  (Γ₁ : VariabilityLanguage V F Bool)
  (Γ₂ : VariabilityLanguage V F ℕ)
  (t : Expression Γ₁ A → Expression Γ₂ A)
  where
  private
    ⟦_⟧₁ = Semantics Γ₁
    ⟦_⟧₂ = Semantics Γ₂
    L₁ = Expression Γ₁
    L₂ = Expression Γ₂
  open VariabilityConstruct (Chc.VLChoice₂.Construct V F)
    renaming (Construct to 2Choice; _⊢⟦_⟧ to _⊢⟦_⟧₂)
  open VariabilityConstruct (Chc.VLChoiceₙ.Construct V F)
    renaming (Construct to NChoice; _⊢⟦_⟧ to _⊢⟦_⟧ₙ)

  -- todo: generalize to any setoid for L₁
  module 2→N-T = 2→N.Translate {Q = F} (Eq.setoid (L₁ A))
  open 2→N-T using (convert)

  -- Composition of two compilers:
  -- first: We convert the binary choice to an n-ary choice via convert, not changing any data
  -- second: We convert all alternatives from one language to another using `mapₙ t`.
  -- This composition is commutative; there is a commuting square
  --   mapₙ t ∘ convert ≅ convert ∘ map₂ t
  -- TODO: Prove this commutativity.
  convert-vl : 2Choice L₁ A → NChoice L₂ A
  convert-vl = mapₙ t ∘ convert

  module Preservation
    (conf : Config₂ F → Configₙ F)
    (fnoc : Configₙ F → Config₂ F)
    (D : F)
    (l r : L₁ A)
    where
    open import Framework.V2.Variants using (VariantSetoid)
    open 2→N-T.Preservation conf fnoc D l r using (convert-preserves; preserves-conf)

    open import Framework.V2.V1Compat using (Conf-Preserves; Fnoc-Preserves; _,_⊢_≚_)

    module IVSet = Data.IndexedSet (VariantSetoid V A)
    module ILSet = Data.IndexedSet (Eq.setoid (L₁ A))
    open ILSet using () renaming (_≅_ to _≋_)
    open IVSet using (⊆-by-index-translation; _≅_; ≐→≅)
    open IVSet.≅-Reasoning

    -- preserves-conf :
    --     ConfSpec D conf
    --   → (c : Config₂ F)
    --   →   (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂) c
    --     ≡ (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ) (conf c)
    -- preserves-conf conv c = {!!}

    -- preserves-fnoc :
    --     FnocSpec D fnoc
    --   → (c : Configₙ F)
    --   →   (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ) c
    --     ≡ (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂) (fnoc c)
    -- preserves-fnoc vnoc c = {!!}

    convert-vl-preserves :
      ∀ (conv : ConfSpec D conf)
      → (vnoc : FnocSpec D fnoc)
      -- Generalize this so that t satisfies a predicate that its semantics preserving
      -- In Framework V1 we have this for translations which are a bit more involved.
      -- But maybe we do not even need the concrete conf translations in the Translation record.
      → (∀ e → Γ₁ , Γ₂ ⊢ e ≚ t e)
      -- → Conf-Preserves Γ₁ Γ₂ l (t l) conf
      -- → Fnoc-Preserves Γ₁ Γ₂ l (t l) fnoc
      -- → Conf-Preserves Γ₁ Γ₂ r (t r) conf
      -- → Fnoc-Preserves Γ₁ Γ₂ r (t r) fnoc
      →   Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂
        ≅ Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ
    proj₁ (convert-vl-preserves conv vnoc t-is-nice) = ⊆-by-index-translation conf left
      where open Eq.≡-Reasoning
            left : (c : Config₂ F)
              →   (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂) c
                ≡ (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ) (conf c)
            left c =
              begin
                (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂) c
              ≡⟨⟩
                ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c
              ≡⟨ Eq.cong (λ x → ⟦ x ⟧₁ c) (preserves-conf conv c) ⟩
                ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c) ⟧₁ c
              ≡⟨ {!!} ⟩ -- t validity here
                ⟦ t (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟧₂ (conf c)
              ≡˘⟨ Eq.cong (λ x → ⟦ x ⟧₂ (conf c)) (Choiceₙ.map-preserves t (convert (D ⟨ l , r ⟩)) (conf c)) ⟩
                ⟦ Choiceₙ.Standard-Semantics (mapₙ t (convert (D ⟨ l , r ⟩))) (conf c) ⟧₂ (conf c)
              ≡⟨⟩
                (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ) (conf c)
              ∎
    proj₂ (convert-vl-preserves conv vnoc t-is-nice) = ⊆-by-index-translation fnoc {!!}
      -- ≅-begin
      --   Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₂
      -- ≅⟨⟩
      --   (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c)
      -- ≐[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₁ c) (preserves-conf conv c) ⟩
      --   (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c) ⟧₁ c)
      -- -- ≅⟨ {!!} ⟩
      --   -- (λ c → ⟦ t (Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c) ⟧₂ (conf c))
      -- -- ≅⟨ {!!} and ⊆-by-index-translation fnoc {!!} ⟩ -- eliminate t because it preserves by assumption
      --   -- (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) c ⟧₁ c)
      -- ≐[ c ]⟨ t-is-nice (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟩
      --   (λ c → ⟦ t (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟧₂ (conf c))
      -- ≅⟨ ? ⟩
      --   (λ c → ⟦ t (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟧₂ c)
      -- ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (Choiceₙ.map-preserves t (convert (D ⟨ l , r ⟩)) c) ⟩
      --   (λ c → ⟦ Choiceₙ.Standard-Semantics (mapₙ t (convert (D ⟨ l , r ⟩))) c ⟧₂ c)
      -- ≅⟨⟩
      --   Γ₂ ⊢⟦ (mapₙ t ∘ convert) (D ⟨ l , r ⟩)) ⟧ₙ
      -- ≅⟨⟩
      --   Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧ₙ
      -- ∎-≅
      -- where open Eq.≡-Reasoning

      --       chc-eq : Choice₂.Standard-Semantics (D ⟨ l , r ⟩) ≋ Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩))
      --       chc-eq = convert-preserves conv vnoc
      --       left : (c : Config₂ F)
      --            →   ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c
      --              ≡ ⟦ t (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟧₂ (conf c)
      --       left c =
      --         begin
      --           ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c
      --         ≡⟨ Eq.cong (λ x → ⟦ x ⟧₁ c) {!proj₁ chc-eq c !} ⟩
      --           ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c) ⟧₁ c
      --         ≡⟨ {!!} ⟩
      --           ⟦ t (Choiceₙ.Standard-Semantics (convert (D ⟨ l , r ⟩)) (conf c)) ⟧₂ (conf c)
      --         ∎
