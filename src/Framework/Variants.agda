module Framework.Variants where

open import Framework.Definitions using (𝕍; 𝔸)
open import Framework.V2.Constructs.Plain.Artifact using (Artifact)

data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} (a : A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

data Rose : 𝕍 where
  artifact : ∀ {A : 𝔸} → Artifact A (Rose A) → Rose A

