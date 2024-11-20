open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Lang.CCC.Properties {Dimension : 𝔽} {A : 𝔸} where

open import Size using (∞)
open import Data.List using ([])
open import Data.List.NonEmpty using (_∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_; _⊢_≣₁_; _,_⊢_≤_)
open import Vatras.Lang.CCC Dimension using (CCC; CCCL; _⟨_⟩)

{-|
Unary choices are mandatory.
-}
D⟨e⟩≣e : ∀ {e : CCC ∞ A} {D : Dimension}
    -----------------------------
  → CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣₁ e
D⟨e⟩≣e _ = refl

-- other way to prove the above

D⟨e⟩⊆e : ∀ {e : CCC ∞ A} {D : Dimension}
    ---------------------------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≤ e
D⟨e⟩⊆e c = c , refl

e⊆D⟨e⟩ : ∀ {e : CCC ∞ A} {D : Dimension}
    ---------------------------------------------------
  → CCCL , CCCL ⊢ e ≤ D ⟨ e ∷ [] ⟩
e⊆D⟨e⟩ c = c , refl

D⟨e⟩≣e' : ∀ {e : CCC ∞ A} {D : Dimension}
    --------------------------------------------------
  → CCCL , CCCL ⊢ D ⟨ e ∷ [] ⟩ ≣ e
D⟨e⟩≣e' {e} {D} = D⟨e⟩⊆e {e} {D} , e⊆D⟨e⟩ {e} {D}
