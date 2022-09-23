# Choice Calculus in Agda

Let's define core choices calculus. Each expression has a non-empty list of sub-expression. Thus, we define non-empty lists first.
```agda
data NonEmptyList {a} (A : Set a) : Set a where
  _✦  : A → NonEmptyList A
  _,_ : A → NonEmptyList A → NonEmptyList A
infixr 5 _,_
```

Now, we can define choice calculus:
```agda
open import Agda.Builtin.String
open import Agda.Builtin.List

data CC (A : Set) : Set where
  Artifact : A → List (CC A) → CC A 
  _⟨_⟩ : String → NonEmptyList (CC A) → CC A
```

Let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
-- smart constructor for plain artifacts
leaf : {A : Set} → A → CC A
leaf a = Artifact a []

walk : CC String
walk = "Ekko" ⟨ leaf "zoom", leaf "pee", leaf "poo"✦ ⟩
```
