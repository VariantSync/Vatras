```agda
{-# OPTIONS --sized-types #-}

module Definitions where
```

# Definitions of Central Abstractions for Variability Languages

```agda
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-l)
open import Data.String using (String; _++_; intersperse)

open import Function using (_∘_; id)
open import Size using (Size; Size<_; ∞)

open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no; isYes)
```

## Languages

We model variability languages as embedded domain specific languages. That is, each variability language is described by a type which in turn is described by the kind `VarLang`. (`Set` denotes the set of all types and `Set₁` denotes the set of all kinds, i.e., the set of all sets of types).
Each language is parameterized in its domain (called _object language_ in choice calculus), such as text, source code, files, whatever.
We model domains, also as types, such as `String`, `ℕ`, or some AST of a programming language.
Each variability language `VarLang` is also parameterized in a size which is irrelevant for studying variation but we need it to ensure that our proofs terminate.
```agda
Domain : Set₁ -- Object Language
Domain = Set

VarLang : Set₁
VarLang = Size → Domain → Set
```

We also model configurations as types but they do not have parameters.
```agda
ConfLang : Set₁
ConfLang = Set
```

## Common Elements
Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
```agda
Artifactˡ : VarLang → Set₁
Artifactˡ L = ∀ {i : Size} {j : Size< i} {A : Domain} → A → List (L j A) → L i A
```

## Semantics

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant.

We model variants as a generic tree structure. To this end, we assume that the domain is not more complex than a tree, which is reasonable since most languages are trees:
```agda
data SizedVariant : VarLang where
  Artifactᵥ : Artifactˡ SizedVariant

Variant : Domain → Set
Variant = SizedVariant ∞
```

Having variants defined, we can now finally formulate the semantics of a variability language:
```agda
open import Util.Existence using (∃-Size)

Semantics : VarLang → ConfLang → Set₁
Semantics L C = ∀ {i : Size} {A : Domain} → L i A → C → Variant A
```

## Assumptions on Variants

The result of a configuration process is a variant and with that, an instance of our `Variant` data type.
The `Variant` type models the tree structure in the domain.
Yet, it is auxiliary and does not denote meaning in within the domain by itself.
We assume though that the structure imposed by the `Variant` exists in the domain and thus is meaningful.
Thus, variants themselves have semantics which embeds them fully into the domain.
In particular, for a variant to really caputure a structure within the domain (and nothing more) it must be isomorphic to the domain.
This means that we can extract the hierarchical structure within an element of our domain to model it explicitly in our `Variant` type; and that `Variant` all hierarchical information necessary to restore the domain element.

To extract the domains hierarchical structure means to divide it into two parts:
- its tree
- and the tree node contents.
With `Variant`, we have a data type that models the `tree` but we miss a model for node contents so far, for which we introduce the `Label` data type:
```agda
Label : Set₁
Label = Set
```
A label is a datatype parameterized in the domain to capture the contents of a particular node in the domains tree hierarchy.

We can now formalize our assumption that it must be legal to split the domain into its hierarchy and contents:
```agda
-- Todo: Reuse generic isomorphism definition
open import Util.SizeJuggle

record ObjectLanguage (A : Bounded) (L : Label) : Set where
  field
    embed   : ∀ {i : Size} → A i → SizedVariant i L
    restore : ∀ {i : Size} → SizedVariant i L → A i
    iso-l   : embed ∘ restore ≗ id
    iso-r   : restore ∘ embed ≗ id
```

## Variant is a Functor

## Equality of Variants

We did not equip variants with bounds yet so we just assume the following functions to terminate.
```agda
root-equality : ∀ {A : Set} {a b : A} {as bs : List (Variant A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → a ≡ b
root-equality refl = refl

subtree-equality : ∀ {A : Set} {a b : A} {as bs : List (Variant A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → as ≡ bs
subtree-equality refl = refl

-- {-# TERMINATING #-}
-- ≡-dec : ∀ {A : Set} → DecidableEquality A → DecidableEquality (Variant A)
-- ≡-dec ≡-dec-A (Artifactᵥ a as) (Artifactᵥ b bs) with ≡-dec-A a b | ≡-dec-l (≡-dec ≡-dec-A) as bs
-- ... | yes a≡b | yes as≡bs = yes (Eq.cong₂ Artifactᵥ a≡b as≡bs)
-- ... | yes a≡b | no ¬as≡bs = no (¬as≡bs ∘ subtree-equality)
-- ... | no ¬a≡b | _         = no (¬a≡b   ∘ root-equality)

-- equals : ∀ {A : Set} → DecidableEquality A → Variant A → Variant A → Bool
-- equals ≡-dec-A V W = isYes (≡-dec ≡-dec-A V W)
```

## Helper Functions and Theorems

### Smart Constructors

```agda
leaf : ∀ {A : Set} → A → Variant A
leaf a = Artifactᵥ a []

leaves : ∀ {A : Set} → List A → List (Variant A)
leaves as = map leaf as
```



Sometimes, it is convenient to invert the order of arguments for variability languages. So instead of speaking of a language `L i A` of size `i` over a domain `A`, we sometimes would like two write `L A i`.
When writing `L A i` we can observer that `L A` is a `Bounded` type which means it is a data type parameterized in only a size:
```agda

flip-VarLang : VarLang → Domain → Bounded
flip-VarLang L A i = L i A
```

### Helpers for dealing with sizes

```agda
open import Data.List.NonEmpty using (List⁺)
open import Size using (↑_)
open import Util.Existence using (∃-Size; _,_)

{-
Creates an Artifact from a list of expressions of a certain size.
The size of the resulting expression is larger by 1.
-}
sequence-sized-artifact : ∀ {A : Domain}
  → {L : VarLang}
  → Weaken (flip-VarLang L A)
  → Artifactˡ L
  → A
  → List⁺ (∃-Size[ i ] (L i A))
    ---------------------------
  → ∃-Size[ i ] (L i A)
sequence-sized-artifact {A} {L} w Artifact a cs =
  let max , es = unify-sizes⁺ w cs
   in
      ↑ max ,
      Artifact {↑ max}
               {i<↑i max}
               {A}
               a
               (i<↑i-list (flip-VarLang L A) max es)
```

### Show

```agda
{-# TERMINATING #-}
show-variant : ∀ {A : Set} → (A → String) → Variant A → String
show-variant s (Artifactᵥ a []) = s a
show-variant s (Artifactᵥ a es@(_ ∷ _)) = s a ++ "-<" ++ (intersperse ", " (map (show-variant s) es)) ++ ">-"
```
