# Choice Calculus in Agda

Let's define core choices calculus
```agda
open import Agda.Builtin.String
open import Agda.Builtin.List

data CC (A : Set) : Set where
  Artifact : A → List (CC A) → CC A
  _⟨_⟩ : String → List (CC A) → CC A
```

Let's build an example
```agda
-- smart constructor for plain artifacts
leaf : {A : Set} → A → CC A
leaf a = Artifact a []

-- example over strings
walk : CC String
walk =  "Ekko" ⟨ leaf "pee" ∷ leaf "poo" ∷ [] ⟩
```
