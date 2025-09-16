open import Vatras.Framework.Definitions
module Vatras.Lang.ADT.Merge
  (V : 𝕍)
  (_+ᵥ_ : ∀ {A} → V A → V A → V A)
  where

open import Data.Bool using (if_then_else_; true; false)
open import Data.Bool.Properties using (if-float)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Vatras.Util.AuxProofs using (if-cong)

import Vatras.Lang.ADT

module Named (F : 𝔽) where
  open Vatras.Lang.ADT F V

  {-|
  Merges two ADTs.
  The resulting ADT denotes all possible compositions of variants, such that configuring the resulting ADT
  is equivalent to configuring both input ADTs and composing the resulting variants (see ⊕-spec below).
  This operations inherits all properties of the variant composition (e.g., commutativity, associativity etc).
  -}
  _⊕_ : ∀ {A} → ADT A → ADT A → ADT A
  leaf l          ⊕ leaf r          = leaf (l +ᵥ r)
  leaf l          ⊕ (E ⟨ el , er ⟩) = E ⟨ leaf l ⊕ el , leaf l ⊕ er ⟩
  (D ⟨ dl , dr ⟩) ⊕ r               = D ⟨ dl ⊕ r , dr ⊕ r ⟩

  ⊕-spec : ∀ {A} (l r : ADT A) (c : Configuration) →
     ⟦ l ⊕ r ⟧ c ≡ ⟦ l ⟧ c +ᵥ ⟦ r ⟧ c
  ⊕-spec (leaf l) (leaf r) c = refl
  ⊕-spec (leaf l) (E ⟨ el , er ⟩) c with c E
  ... | true = ⊕-spec (leaf l) el c
  ... | false = ⊕-spec (leaf l) er c
  ⊕-spec (D ⟨ dl , dr ⟩) r c with c D
  ... | true  = ⊕-spec dl r c
  ... | false = ⊕-spec dr r c

  ---- Properties ----
  -- The merge operator inherits
  -- properties of the variant composition operator.
  --------------------

  -- import Algebra.Definitions
  -- module Eq (A : 𝔸) where
  --   open Algebra.Definitions (_≡_ {A = V A}) using (Commutative) public

  -- module Sem (A : 𝔸) where
  --   open Algebra.Definitions (_⊢_≣₁_ {A} ADTL) using (Commutative) public

  -- ⊕-comm : ∀ {A} → Eq.Commutative A _+ᵥ_ -> Sem.Commutative A _⊕_
  ⊕-comm :
    (∀ {A} (v w : V A) → v +ᵥ w ≡ w +ᵥ v) →
    ---------------------------------------------
    (∀ {A} (l r : ADT A) → ⟦ l ⊕ r ⟧ ≗ ⟦ r ⊕ l ⟧)
  ⊕-comm +ᵥ-comm l r c =
      ⟦ l ⊕ r ⟧ c
    ≡⟨ ⊕-spec l r c ⟩
      ⟦ l ⟧ c +ᵥ ⟦ r ⟧ c
    ≡⟨ +ᵥ-comm (⟦ l ⟧ c) (⟦ r ⟧ c) ⟩
      ⟦ r ⟧ c +ᵥ ⟦ l ⟧ c
    ≡⟨ ⊕-spec r l c ⟨
      ⟦ r ⊕ l ⟧ c
    ∎

module Prop (F : 𝔽) where
  open import Vatras.Data.Prop
  open import Vatras.Lang.ADT.Prop F V
  open Named (Prop F) using (_⊕_) public

  ⊕-specₚ : ∀ {A} (l r : PropADT A) (c : Assignment F) →
     ⟦ l ⊕ r ⟧ₚ c ≡ ⟦ l ⟧ₚ c +ᵥ ⟦ r ⟧ₚ c
  ⊕-specₚ (leaf v) (leaf r) c = refl
  ⊕-specₚ (leaf l) (E ⟨ el , er ⟩) c with eval E c
  ... | true  = ⊕-specₚ (leaf l) el c
  ... | false = ⊕-specₚ (leaf l) er c
  ⊕-specₚ (D ⟨ dl , dr ⟩) r c with eval D c
  ... | true = ⊕-specₚ dl r c
  ... | false = ⊕-specₚ dr r c
