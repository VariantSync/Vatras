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
    ∀ (E : 𝔼) → Syntax ∈ₛ E
    → {A : 𝔸} → A
    → {F : 𝔽} → E A
  make-leaf _ mkLeaf a {F} = cons mkLeaf {F = F} (leaf a)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → Syntax ∈ₛ V → ℂ-Semantics V F S Syntax
  Semantics {F = F} leaf∈V _ _ l _ = cons leaf∈V {F = F} l

  Construct : ∀ (V : 𝕍) (F : 𝔽) (S : 𝕊)
    → Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct _ _ _ mkLeaf = record
    { Construct = Syntax
    ; construct-semantics = Semantics mkLeaf
    }

  Leaf∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons Leaf∈ₛGrulerVariant (leaf a) = asset a
  snoc Leaf∈ₛGrulerVariant (asset a) = just (leaf a)
  snoc Leaf∈ₛGrulerVariant (_ ∥ _) = nothing
  id-l Leaf∈ₛGrulerVariant (leaf _) = refl

module VLParallelComposition where
  Syntax : ℂ
  Syntax _ E A = ParallelComposition (E A)

  Semantics : ∀ {V : 𝕍} {F : 𝔽} {S : 𝕊} → Syntax ∈ₛ V → ℂ-Semantics V F S Syntax
  Semantics {F = F} leaf∈V _ (syn E with-sem ⟦_⟧) (l ∥ r) c = cons leaf∈V {F = F} (⟦ l ⟧ c ∥ ⟦ r ⟧ c)

  Construct : ∀ (V : 𝕍) (F : 𝔽) (S : 𝕊)
    → Syntax ∈ₛ V
    → VariabilityConstruct V F S
  Construct _ _ _ mkPC = record
    { Construct = Syntax
    ; construct-semantics = Semantics mkPC
    }

  ParallelComposition∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons ParallelComposition∈ₛGrulerVariant (l ∥ r) = l ∥ r
  snoc ParallelComposition∈ₛGrulerVariant (asset a) = nothing
  snoc ParallelComposition∈ₛGrulerVariant (l ∥ r) = just (l ∥ r)
  id-l ParallelComposition∈ₛGrulerVariant (l ∥ r) = refl
