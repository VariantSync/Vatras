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
  Syntax _ = Leaf

  make-leaf :
    ∀ {E : 𝔼} → Syntax ∈ₛ E
    → {A : 𝔸} → A
    → E A
  make-leaf mkLeaf a = cons mkLeaf (leaf a)

  elim-leaf : ∀ {V} → Syntax ∈ₛ V → ∀ {A} → Leaf A → V A
  elim-leaf leaf∈V l = cons leaf∈V l

  Semantics : ∀ {V S} → Syntax ∈ₛ V → ℂ-Semantics V S Syntax
  Semantics leaf∈V _ _ l _ = elim-leaf leaf∈V l

  Construct : ∀ (V : 𝕍) (S : 𝕊)
    → Syntax ∈ₛ V
    → VariabilityConstruct V S
  Construct V S mkLeaf = record
    { Construct = Syntax
    ; construct-semantics = Semantics {V} {S} mkLeaf
    }

  Leaf∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons Leaf∈ₛGrulerVariant (leaf a) = asset a
  snoc Leaf∈ₛGrulerVariant (asset a) = just (leaf a)
  snoc Leaf∈ₛGrulerVariant (_ ∥ _) = nothing
  id-l Leaf∈ₛGrulerVariant (leaf _) = refl

module VLParallelComposition where
  Syntax : ℂ
  Syntax E A = ParallelComposition (E A)

  Semantics : ∀ {V : 𝕍} {S : 𝕊} → Syntax ∈ₛ V → ℂ-Semantics V S Syntax
  Semantics leaf∈V _ (syn E with-sem ⟦_⟧) (l ∥ r) c = cons leaf∈V (⟦ l ⟧ c ∥ ⟦ r ⟧ c)

  Construct : ∀ (V : 𝕍) (S : 𝕊)
    → Syntax ∈ₛ V
    → VariabilityConstruct V S
  Construct V S mkPC = record
    { Construct = Syntax
    ; construct-semantics = Semantics {V} {S} mkPC
    }

  ParallelComposition∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons ParallelComposition∈ₛGrulerVariant (l ∥ r) = l ∥ r
  snoc ParallelComposition∈ₛGrulerVariant (asset a) = nothing
  snoc ParallelComposition∈ₛGrulerVariant (l ∥ r) = just (l ∥ r)
  id-l ParallelComposition∈ₛGrulerVariant (l ∥ r) = refl
