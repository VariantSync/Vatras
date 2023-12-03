module Framework.V2.Language where

open import Relation.Binary using (Setoid)
open import Level using (suc; _⊔_)

𝔻 : ∀ {ℓ₁ ℓ₂} → Set (suc (ℓ₁ ⊔ ℓ₂))
𝔻 {ℓ₁} {ℓ₂} = Setoid ℓ₁ ℓ₂

record Language {ℓ₁ ℓ₂ ℓ₃} (SemanticDomain : 𝔻 {ℓ₂} {ℓ₃}) : Set (suc (ℓ₁) where
  open Setoid SemanticDomain using (Carrier)
  field
    Syntax : Set ℓ₁
    Semantics : Syntax → Carrier
open Language

-- record Compiler (A B : Language) where
--   field
--     compile : A → B
--     correct : ∀ {a : Syntax A} → Semantics
