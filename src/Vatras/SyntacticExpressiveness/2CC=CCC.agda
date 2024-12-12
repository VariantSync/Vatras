open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.SyntacticExpressiveness.2CC=CCC (F : 𝔽) where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Size using (∞)

open import Vatras.Util.Nat.AtLeast using (sucs)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.SyntacticExpressiveness using (_=Size_; ≤Size-transitive)
open import Vatras.SyntacticExpressiveness.Sizes F using (Sized2CC; SizedCCC)
open import Vatras.SyntacticExpressiveness.2CC=2CC using (2CC=2CC; NCC=2CC)
open import Vatras.SyntacticExpressiveness.2CC≤CCC F using (2CC≤CCC)
open import Vatras.SyntacticExpressiveness.CCC≤NCC F using (CCC≤NCC)

2CC=CCC :
  ∀ (f : F × ℕ → F)
  → (f⁻¹ : F → F × ℕ)
  → f⁻¹ ∘ f ≗ id
  → f ∘ f⁻¹ ≗ id
  → Sized2CC =Size SizedCCC
2CC=CCC f f⁻¹ f⁻¹∘f≗id f∘f⁻¹≗id =
    ≤Size-transitive (proj₁ (2CC=2CC f f⁻¹ f⁻¹∘f≗id f∘f⁻¹≗id)) 2CC≤CCC
  , ≤Size-transitive (CCC≤NCC (sucs zero)) (proj₁ NCC=2CC)
