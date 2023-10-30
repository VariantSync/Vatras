module Framework.V2.Constructs.GrulerArtifacts where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Level using (Lift; lift)

open import Framework.V2.Definitions hiding (Semantics)
open import Framework.V2.Variants

-- this is just a value
data Leaf {ℓ} (A : Set ℓ) : Set ℓ where
  leaf : (a : A) → Leaf A

-- this is just a pair
record ParallelComposition {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _∥_
  field
    l : A
    r : A

module VLLeaf {ℓ ℓᶠ ℓˢ} where
  Syntax : ℂ ℓ ℓᶠ
  Syntax _ _ A = Lift ℓᶠ (Leaf A)

  make-leaf :
    ∀ {F : 𝔽 ℓᶠ} {E : 𝔼 ℓ} → F ⊢ Syntax ∈ₛ E
    → {A : 𝔸 ℓ} → A
    → E A
  make-leaf mkLeaf a = cons mkLeaf (lift (leaf a))

  elim-leaf : ∀ {V} (F : 𝔽 ℓᶠ) → F ⊢ Syntax ∈ₛ V → ∀ {A} → Leaf A → V A
  elim-leaf _ leaf∈V l = cons leaf∈V (lift l)

  Semantics : ∀ {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ}
    → F ⊢ Syntax ∈ₛ V
    → ℂ-Semantics V F S Syntax
  Semantics {F = F} leaf∈V _ _ (lift l) _ = elim-leaf F leaf∈V l

  Construct : ∀ (V : 𝕍 ℓ) (F : 𝔽 ℓᶠ) (S : 𝕊 ℓˢ)
    → F ⊢ Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct _ _ _ mkLeaf = record
    { Construct = Syntax
    ; construct-semantics = Semantics mkLeaf
    }

  Leaf∈ₛGrulerVariant : ∀ {F} → F ⊢ Syntax ∈ₛ GrulerVariant
  cons Leaf∈ₛGrulerVariant (lift (leaf a)) = asset a
  snoc Leaf∈ₛGrulerVariant (asset a) = just (lift (leaf a))
  snoc Leaf∈ₛGrulerVariant (_ ∥ _) = nothing
  id-l Leaf∈ₛGrulerVariant (lift (leaf _)) = refl

module VLParallelComposition {ℓ ℓᶠ ℓˢ} where
  Syntax : ℂ ℓ ℓᶠ
  Syntax _ E A = Lift ℓᶠ (ParallelComposition (E A))

  Semantics : ∀ {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ}
    → F ⊢ Syntax ∈ₛ V
    → ℂ-Semantics V F S Syntax
  Semantics leaf∈V _ (syn E with-sem ⟦_⟧) (lift (l ∥ r)) c = cons leaf∈V (lift (⟦ l ⟧ c ∥ ⟦ r ⟧ c))

  Construct : ∀ (V : 𝕍 ℓ) (F : 𝔽 ℓᶠ) (S : 𝕊 ℓˢ)
    → F ⊢ Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct _ _ _ mkPC = record
    { Construct = Syntax
    ; construct-semantics = Semantics mkPC
    }

  ParallelComposition∈ₛGrulerVariant : ∀ {F} → F ⊢ Syntax ∈ₛ GrulerVariant
  cons ParallelComposition∈ₛGrulerVariant (lift (l ∥ r)) = l ∥ r
  snoc ParallelComposition∈ₛGrulerVariant (asset a) = nothing
  snoc ParallelComposition∈ₛGrulerVariant (l ∥ r) = just (lift (l ∥ r))
  id-l ParallelComposition∈ₛGrulerVariant (lift (l ∥ r)) = refl
