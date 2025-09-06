open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Succinctness.Relations.2CC=CCC (F : 𝔽) where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Size using (∞)

open import Vatras.Util.Nat.AtLeast using (sucs)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_=ₛ_; ≤ₛ-transitive)
open import Vatras.Succinctness.Sizes using (Sized2CC; SizedCCC)
open import Vatras.Succinctness.Relations.2CC=2CC using (2CC=2CC; NCC=2CC)
open import Vatras.Succinctness.Relations.2CC≤CCC F using (2CC≤CCC)
open import Vatras.Succinctness.Relations.CCC≤NCC F using (CCC≤NCC)

open import Vatras.Translation.Lang.Transitive.CCC-to-2CC using (2CC≽CCC)
open import Vatras.Translation.Lang.2CC.Rename using (2CC-rename≽2CC)
open import Vatras.Translation.Lang.NCC-to-CCC using (CCC≽NCC)
open import Vatras.Translation.Lang.2CC-to-NCC using (NCC≽2CC)

2CC=CCC :
  ∀ (f : F × ℕ → F)
  → (f⁻¹ : F → F × ℕ)
  → f⁻¹ ∘ f ≗ id
  → f ∘ f⁻¹ ≗ id
  → Sized2CC F =ₛ SizedCCC F
2CC=CCC f f⁻¹ f⁻¹∘f≗id f∘f⁻¹≗id =
    ≤ₛ-transitive (2CC-rename≽2CC f f⁻¹ f⁻¹∘f≗id) 2CC≽CCC (proj₁ (2CC=2CC f f⁻¹ f⁻¹∘f≗id f∘f⁻¹≗id)) 2CC≤CCC
  , ≤ₛ-transitive (CCC≽NCC (sucs zero)) (NCC≽2CC (sucs zero)) (CCC≤NCC (sucs zero)) (proj₁ NCC=2CC)
