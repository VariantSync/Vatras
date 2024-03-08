open import Framework.Definitions

module Translation.Construct.2Choice-to-Choice-VL where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)

-- open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_; refl)

import Data.IndexedSet

open import Framework.VariabilityLanguage
open import Framework.Construct
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Function using (to-is-Embedding)

import Translation.Construct.2Choice-to-Choice as 2Choice-to-Choice
open 2Choice-to-Choice using (ConfContract; FnocContract)

open import Construct.Choices

module Translate {Q : 𝔽} {V : 𝕍} {A : 𝔸}
  (Γ₁ Γ₂ : VariabilityLanguage V)
  (extract₁ : Compatible (VL2Choice.Construct V Q) Γ₁)
  (t : LanguageCompiler Γ₁ Γ₂)
  (confi : 2Choice.Config Q → Choice.Config Q)
  (fnoci : Choice.Config Q → 2Choice.Config Q)
  where
  private
    L₁   = Expression Γ₁
    ⟦_⟧₁ = Semantics  Γ₁
    L₂   = Expression Γ₂
    ⟦_⟧₂ = Semantics  Γ₂
    open LanguageCompiler t

  -- TODO: Generalize to any setoids over L₁ or L₂.
  module 2Choice-to-Choice-T₁ = 2Choice-to-Choice.Translate {Q} (Eq.setoid (L₁ A))
  open 2Choice-to-Choice-T₁ using () renaming (convert to convert₁)
  module 2Choice-to-Choice-T₂ = 2Choice-to-Choice.Translate {Q} (Eq.setoid (L₂ A))
  open 2Choice-to-Choice-T₂ using () renaming (convert to convert₂)

  {-|
  Composition of two compilers:
  First, we convert all alternatives from one language to another using `map₂ compile`.
  Second, we convert the binary choice to an n-ary choice via convert, not changing any data.
  The order of these steps does not matter, as proven by `convert-comm` below.
  -}
  compile-convert : VL2Choice.Syntax Q L₁ A → VLChoice.Syntax Q L₂ A
  compile-convert = convert₂ ∘ 2Choice.map compile

  {-|
  The same compiler as compile-convert, but the steps are executed in the other order.
  -}
  convert-compile : VL2Choice.Syntax Q L₁ A → VLChoice.Syntax Q L₂ A
  convert-compile = Choice.map compile ∘ convert₁

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
