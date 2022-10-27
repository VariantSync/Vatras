```agda
module cc where

open import Function.Base

open import Data.String.Base hiding (toList)
open import Data.Nat.Base
open import Data.List.Base renaming (map to mapl) hiding (_++_)
open import Data.List.NonEmpty.Base renaming (map to mapl⁺)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Extensionality
```

# Choice Calculus in Agda

Let's define core choices calculus as defined in Eric's phd thesis:
```agda
Dimension : Set
Dimension = String

Tag : Set
Tag = ℕ

data CC (A : Set) : Set where
  Artifact : A → List (CC A) → CC A
  _⟨_⟩ : Dimension → List⁺ (CC A) → CC A
```

Choice calculus has denotational semantics, introduced by Eric in the TOSEM paper and his PhD thesis.
Semantics for choice calculus can be defined in different ways.
In his phd thesis, Eric defined the semantics to be the set of all variants described by the expression.
So the semantic domain was a set of choice calculus expressions without any choices.
We can encode a choice calculus expression without choices at the type level:
```agda
data Variant (A : Set) : Set where
  Artifactᵥ : A → List (Variant A) → Variant A
```
This is basically just a tree structure of artifacts.

An equivalent definition produces a configuration function `Config → Variant` that generates variants from configurations.
This definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags, according to Eric's phd thesis:
```agda
Configuration : Set
Configuration = Dimension → Tag
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to introduce complex error handling and we cannot easily define a configuration to only produce tags within ranges.

```agda
open import Data.Fin.Base
open import AuxProofs

{-|
Clamps a tag at the given length.
Takes a length n as implicit first argument and a proof that this length is positive as second argument.
In case the given tag is smaller than the given length, the tag is returned, otherwise the length - 1.
Returns an index which is proven to be smaller than the given length.
-}
clampTagWithin : {n : ℕ} → {NonZero n} → Tag → Fin n
clampTagWithin {suc n} {nz} = minFinFromLimit n

-- Selects the alternative at the given tag.
-- Agda can implicitly prove that the length of the list is positive, because it is a non-empty list, and by type inference, it supplies the list length to clampWithin.
selectAlternative : {A : Set} → Tag → List⁺ A → A
selectAlternative t alts⁺ = lookup (toList alts⁺) (clampTagWithin t)

{-# TERMINATING #-}
ccsem : {A : Set} → CC A → Configuration → Variant A
ccsem (Artifact a es) c = Artifactᵥ a (mapl (flip ccsem c) es)
ccsem (D ⟨ alternatives ⟩) c = ccsem (selectAlternative (c D) alternatives) c
```

Let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
-- smart constructor for plain artifacts
leaf : {A : Set} → A → CC A
leaf a = Artifact a []

cc_example_walk : CC String
cc_example_walk = "Ekko" ⟨ leaf "zoom" ∷ leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩

cc_example_walk_zoom : Variant String
cc_example_walk_zoom = ccsem cc_example_walk (λ {"Ekko" → 0; _ → 0})
```

Print the example:
```agda
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

{-# TERMINATING #-}
showVariant : Variant String → String
showVariant (Artifactᵥ a es) = a ++ "-<" ++ (Data.List.Base.foldl _++_ "" (mapl showVariant es)) ++ ">-"

main : IO ⊤
main = putStrLn (showVariant cc_example_walk_zoom)
```

In the following we introduce normal forms for choice calculus expressions.
We express each normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.

An algebaric decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ and the 1997 ADD paper, ADDs are defined to be binary.
```agda
data ADD (A : Set) : Set where
  Product : A → ADD A -- ModelBase
  Choice : Dimension → ADD A → ADD A → ADD A -- ModelChoice, has a presence condition here instead of a dimension
```

To convert to product normal form, it is easier to first convert to binary normal form of choice calculus.
Every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.
```agda
data CC₂ (A : Set) : Set where
  Artifact₂ : A → List (CC₂ A) → CC₂ A
  _⟨_,_⟩₂ : Dimension → CC₂ A → CC₂ A → CC₂ A

{-# TERMINATING #-} -- Todo: Can we prove this terminating?
toCC : {A : Set} → CC₂ A → CC A
toCC (Artifact₂ a es) = Artifact a (mapl toCC es)
toCC (D ⟨ l , r ⟩₂) = D ⟨ (toCC l) ∷ (toCC r) ∷ [] ⟩

newDim : Dimension → Dimension
newDim s = s ++ "'"

{-# TERMINATING #-}
toCC₂ : {A : Set} → CC A → CC₂ A
-- Leave structures unchanged
toCC₂ (Artifact a es) = Artifact₂ a (mapl toCC₂ es)
-- Use the idempotency rule to unwrap unary choices
-- TODO: Prove that this is legal
toCC₂ (D ⟨ e ∷ [] ⟩) = toCC₂ e
-- Leave binary choices unchanged
toCC₂ (D ⟨ then ∷ elze ∷ [] ⟩) = D ⟨ toCC₂ then , toCC₂ elze ⟩₂
-- Perform recursive nesting on choices with arity n > 2.
toCC₂ (D ⟨ e₁ ∷ e₂ ∷ es ⟩) = D ⟨ toCC₂ e₁ , toCC₂ ((newDim D) ⟨ e₂ ∷ es ⟩) ⟩₂

```
