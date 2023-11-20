open import Framework.V2.Definitions

module Framework.V2.Translation.Construct.2Choice-to-NChoice-VL where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)

-- open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_; refl)

import Data.IndexedSet

open import Framework.V2.Variants
open import Framework.V2.Compiler using (LanguageCompiler; Stable)

import Framework.V2.Translation.Construct.2Choice-to-NChoice as 2→N
open 2→N using (ConfContract; FnocContract)

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂; map to map₂)
open Chc.Choiceₙ using () renaming (Config to Configₙ; map to mapₙ)

module Translate {V : 𝕍} {Q : Set} {A : 𝔸}
  (Γ₁ : VariabilityLanguage V (Config₂ Q))
  (Γ₂ : VariabilityLanguage V (Configₙ Q))
  (t : LanguageCompiler Γ₁ Γ₂)
  where
  private
    L₁   = Expression Γ₁
    ⟦_⟧₁ = Semantics  Γ₁
    L₂   = Expression Γ₂
    ⟦_⟧₂ = Semantics  Γ₂
    open LanguageCompiler t

  open VariabilityConstruct (Chc.VLChoice₂.Construct Q V)
    renaming (Construct to 2Choice; _⊢⟦_⟧ to _⊢⟦_⟧₁)
  open VariabilityConstruct (Chc.VLChoiceₙ.Construct Q V)
    renaming (Construct to NChoice; _⊢⟦_⟧ to _⊢⟦_⟧₂)

  -- TODO: Generalize to any setoids over L₁ or L₂.
  module 2→N-T₁ = 2→N.Translate {Q} (Eq.setoid (L₁ A))
  open 2→N-T₁ using () renaming (convert to convert₁)
  module 2→N-T = 2→N.Translate {Q} (Eq.setoid (L₂ A))
  open 2→N-T using () renaming (convert to convert₂)

  {-|
  Composition of two compilers:
  First, we convert all alternatives from one language to another using `map₂ compile`.
  Second, we convert the binary choice to an n-ary choice via convert, not changing any data.
  The order of these steps does not matter, as proven by `convert-comm` below.
  -}
  compile-convert : 2Choice L₁ A → NChoice L₂ A
  compile-convert = convert₂ ∘ map₂ compile

  {-|
  The same compiler as compile-convert, but the steps are executed in the other order.
  -}
  convert-compile : 2Choice L₁ A → NChoice L₂ A
  convert-compile = mapₙ compile ∘ convert₁

  {-|
  Proof that the following square commutes.
  This means that it does not matter in which order we
    - convert a binary to an n-ary choice,
    - compile subterms.

  Algebraically:
    mapₙ compile ∘ convert ≗ convert ∘ map₂ compile

  Graphically:
    binary L₁ ── convert ──→ nary L₁
      |                        |
      | map₂ compile           | mapₙ compile
      ↓                        ↓
    binary L₂ ── convert ──→ nary L₂
  -}
  convert-comm : convert-compile ≗ compile-convert
  convert-comm _ = refl

  module Preservation
    (D : Q)
    (l r : L₁ A)
    where
    open 2→N-T.Preservation conf fnoc using (convert-preserves)

    module VSet = IVSet V A
    open VSet using (_≅[_][_]_)
    open VSet.≅[]-Reasoning

    convert-compile-preserves :
      ∀ (conv : ConfContract D conf)
      → (vnoc : FnocContract D fnoc)
      → Stable config-compiler
      → (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁) ≅[ conf ][ fnoc ] (Γ₂ ⊢⟦ convert-compile (D ⟨ l , r ⟩) ⟧₂)
    convert-compile-preserves conv vnoc stable =
      ≅[]-begin
        Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c)
      ≅[]⟨ VLChoice₂.map-compile-preserves Q t (D ⟨ l , r ⟩) stable ⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (map₂ compile (D ⟨ l , r ⟩)) (fnoc c) ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ compile l , compile r ⟩) (fnoc c) ⟧₂ c)
        -- TODO: Figure out why we need only proj₂ and not also proj₁ in this proof.
      ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (proj₂ (convert-preserves (map₂ compile (D ⟨ l , r ⟩)) conv vnoc) c) ⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert₂ (D ⟨ compile l , compile r ⟩)) c ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert₂ (map₂ compile (D ⟨ l , r ⟩))) c ⟧₂ c)
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert₂ (map₂ compile (D ⟨ l , r ⟩)) ⟧₂
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert-compile (D ⟨ l , r ⟩) ⟧₂
      ≅[]-∎

    compile-convert-preserves :
      ∀ (conv : ConfContract D conf)
      → (vnoc : FnocContract D fnoc)
      → Stable config-compiler
      → (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁) ≅[ conf ][ fnoc ] (Γ₂ ⊢⟦ compile-convert (D ⟨ l , r ⟩) ⟧₂)
    compile-convert-preserves conv vnoc stable =
      ≅[]-begin
        Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁
      ≅[]⟨ convert-compile-preserves conv vnoc stable ⟩
        Γ₂ ⊢⟦ convert-compile (D ⟨ l , r ⟩) ⟧₂
      ≐[ c ]⟨ Eq.cong (λ eq → ⟦ Choiceₙ.Standard-Semantics eq c ⟧₂ c) (convert-comm (D ⟨ l , r ⟩)) ⟩
        Γ₂ ⊢⟦ compile-convert (D ⟨ l , r ⟩) ⟧₂
      ≅[]-∎
