{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.Construct.NestedChoice-to-2Choice where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; proj₁; Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

open import Function.Base using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.Annotation.IndexedName using (IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choiceₙ using () renaming (Config to Configₙ)
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂)
open Chc.VLChoice₂ using () renaming (Syntax to 2Choice; Semantics to 2Choice-sem)
open import Framework.V2.Translation.Construct.NChoice-to-2Choice hiding (NConfig; 2Config)

NConfig : Set → Set
NConfig Q = Configₙ Q

2Config : Set → Set
2Config Q = Σ (Config₂ (IndexedName Q)) at-least-true-once

2Choice' : ℂ
2Choice' F E A = 2Choice (IndexedName F) E A

ChoiceConstructor : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V F 2Config
ChoiceConstructor V F = con 2Choice' with-sem sem V F
  where
  sem : ∀ (V : 𝕍) (F : 𝔽) → ℂ-Semantics V F 2Config 2Choice'
  sem V F fnoc Γ cons conf = 2Choice-sem V (IndexedName F) (proj₁ ∘ fnoc) Γ cons conf

module Embed
  {V : 𝕍} {F : 𝔽} {A : 𝔸}
  (Γ : VariabilityLanguage V F 2Config)
  (constr : (ChoiceConstructor V F) ⟦∈⟧ Γ)
  where

  open Translate {F} (Eq.setoid (Expression Γ A))
  open Data.IndexedSet (Eq.setoid (V A)) using (_≅_; ≗→≅)

  embed : ∀ {i} → NestedChoice i → Expression Γ A
  embed (val v) = v
  embed (nchc c) = cons (make constr) (map (embed) c)
    where
    open Chc.Choice₂ using (map)

  embed-preserves : ∀ {i}
    → (e : NestedChoice i)
    → Semantics Γ (embed e) ≅ λ c → Semantics Γ (⟦ e ⟧ c) c
  embed-preserves e = ≗→≅ (induction e)
    where
    induction : ∀ {i}
      → (e : NestedChoice i)
      → Semantics Γ (embed e) ≗ λ c → Semantics Γ (⟦ e ⟧ c) c
    induction (val v) c = refl
    induction (nchc (dim ⟨ l , r ⟩)) c
      rewrite preservation constr (dim ⟨ embed l , embed r ⟩) c
      with evalConfig c dim
    ... | true = induction l c
    ... | false = induction r c
