open import Framework.V2.Definitions

module Framework.V2.Translation.2Choice-to-NChoice-VL {F : 𝔽} where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)

-- open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

open import Framework.V2.Variants
open import Framework.V2.Compiler using (LanguageCompiler; Stable)

import Framework.V2.Translation.2Choice-to-NChoice as 2→N
open 2→N using (ConfSpec; FnocSpec)

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂; map to map₂)

module Translate {F : 𝔽} {V : 𝕍} {A : 𝔸}
  (Γ₁ : VariabilityLanguage V F Bool)
  (Γ₂ : VariabilityLanguage V F ℕ)
  (t : LanguageCompiler Γ₁ Γ₂)
  where
  private
    L₁   = Expression Γ₁
    ⟦_⟧₁ = Semantics  Γ₁
    L₂   = Expression Γ₂
    ⟦_⟧₂ = Semantics  Γ₂
    open LanguageCompiler t

  open VariabilityConstruct (Chc.VLChoice₂.Construct F)
    renaming (Construct to 2Choice; _⊢⟦_⟧ to _⊢⟦_⟧₁)
  open VariabilityConstruct (Chc.VLChoiceₙ.Construct F)
    renaming (Construct to NChoice; _⊢⟦_⟧ to _⊢⟦_⟧₂)

  -- TODO: Generalize to any setoid for L₁.
  module 2→N-T = 2→N.Translate {Q = F} (Eq.setoid (L₂ A))
  open 2→N-T using (convert)

  -- Composition of two compilers:
  -- First, we convert all alternatives from one language to another using `map₂ compile`.
  -- Second, we convert the binary choice to an n-ary choice via convert, not changing any data.
  -- This composition is commutative; there is a commuting square:
  --   mapₙ compile ∘ convert ≅ convert ∘ map₂ compile
  -- TODO: Prove this commutativity.
  convert-vl : 2Choice F L₁ A → NChoice F L₂ A
  convert-vl = convert ∘ map₂ compile

  module Preservation
    (D : F)
    (l r : L₁ A)
    where
    open 2→N-T.Preservation conf fnoc using (convert-preserves)

    module VSet = IVSet V A
    open VSet using (_≅[_][_]_)
    open VSet.≅[]-Reasoning

    convert-vl-preserves :
      ∀ (conv : ConfSpec D conf)
      → (vnoc : FnocSpec D fnoc)
      → Stable config-compiler
      → (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁) ≅[ conf ][ fnoc ] (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧₂)
    convert-vl-preserves conv vnoc stable =
      ≅[]-begin
        Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c)
      ≅[]⟨ VLChoice₂.map-compile-preserves t (D ⟨ l , r ⟩) stable ⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (map₂ compile (D ⟨ l , r ⟩)) (fnoc c) ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ compile l , compile r ⟩) (fnoc c) ⟧₂ c)
        -- TODO: Figure out why we need only proj₂ and not also proj₁ in this proof.
      ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (proj₂ (convert-preserves D (compile l) (compile r) conv vnoc) c) ⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ compile l , compile r ⟩)) c ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (map₂ compile (D ⟨ l , r ⟩))) c ⟧₂ c)
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert (map₂ compile (D ⟨ l , r ⟩)) ⟧₂
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧₂
      ≅[]-∎
