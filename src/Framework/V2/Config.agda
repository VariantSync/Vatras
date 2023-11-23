open import Level using (Level; suc)
open import Relation.Binary using (Setoid)
module Framework.V2.Config
  {c ℓ : Level}
  (S : Setoid c ℓ)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Function using (_∘_; id; Injective)

open import Framework.V2.FunctionLanguage S

ConfigurationLanguage : Set (suc c)
ConfigurationLanguage = FunctionLanguage

Config            = Expression
FeatureLanguage   = Input
SelectionLanguage = Setoid.Carrier S
lookup            = Semantics

Stable = Embedding
