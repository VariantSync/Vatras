module Framework.V2.Constructs.GrulerArtifacts where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

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

module VLLeaf where
  Syntax : ℂ
  Syntax _ _ A = Leaf A

  make-leaf :
    ∀ {F : 𝔽} {E : 𝔼} → F ⊢ Syntax ∈ₛ E
    → {A : 𝔸} → A
    → E A
  make-leaf mkLeaf a = cons mkLeaf (leaf a)

  elim-leaf : ∀ {V} (F : 𝔽) → F ⊢ Syntax ∈ₛ V → ∀ {A} → Leaf A → V A
  elim-leaf _ leaf∈V l = cons leaf∈V l

  Semantics : ∀ {V F S} → F ⊢ Syntax ∈ₛ V → ℂ-Semantics V F S Syntax
  Semantics {F = F} leaf∈V _ _ l _ = elim-leaf F leaf∈V l

  Construct : ∀ (V : 𝕍) (F : 𝔽) (S : 𝕊)
    → F ⊢ Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct V F S mkLeaf = record
    { Construct = Syntax
    ; construct-semantics = Semantics {V} {F} {S} mkLeaf
    }

  Leaf∈ₛGrulerVariant : ∀ {F} → F ⊢ Syntax ∈ₛ GrulerVariant
  cons Leaf∈ₛGrulerVariant (leaf a) = asset a
  snoc Leaf∈ₛGrulerVariant (asset a) = just (leaf a)
  snoc Leaf∈ₛGrulerVariant (_ ∥ _) = nothing
  id-l Leaf∈ₛGrulerVariant (leaf _) = refl

module VLParallelComposition where
  Syntax : ℂ
  Syntax _ E A = ParallelComposition (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → F ⊢ Syntax ∈ₛ V → ℂ-Semantics V F S Syntax
  Semantics leaf∈V _ (syn E with-sem ⟦_⟧) (l ∥ r) c = cons leaf∈V (⟦ l ⟧ c ∥ ⟦ r ⟧ c)

  Construct : ∀ (V : 𝕍) (F : 𝔽) (S : 𝕊)
    → F ⊢ Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct V F S mkPC = record
    { Construct = Syntax
    ; construct-semantics = Semantics {V} {F} {S} mkPC
    }

  ParallelComposition∈ₛGrulerVariant : ∀ {F} → F ⊢ Syntax ∈ₛ GrulerVariant
  cons ParallelComposition∈ₛGrulerVariant (l ∥ r) = l ∥ r
  snoc ParallelComposition∈ₛGrulerVariant (asset a) = nothing
  snoc ParallelComposition∈ₛGrulerVariant (l ∥ r) = just (l ∥ r)
  id-l ParallelComposition∈ₛGrulerVariant (l ∥ r) = refl
