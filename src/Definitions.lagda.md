```agda
{-# OPTIONS --sized-types #-}

module Definitions where
```

# Definitions of Central Abstractions for Variability Languages

```agda
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-l)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String; _++_; intersperse)
open import Data.Product using (_×_; ∃-syntax; _,_)

open import Function using (_∘_)
open import Level using (0ℓ) renaming (suc to ℓ-suc)
open import Size using (Size; ↑_; _⊔ˢ_; ∞)

open import Relation.Nullary.Decidable using (Dec; yes; no; isYes; False; toWitnessFalse)
open import Relation.Binary using (Setoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)

import Data.Multiset as MSet
open import Util.Existence using (∃-Size)
```

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

Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
```agda
Artifactˡ : VarLang → Set₁
Artifactˡ L = ∀ {i : Size} {A : Domain} → A → List (L i A) → L (↑ i) A
```

We also model configurations as types but they do not have parameters.
```agda
ConfLang : Set₁
ConfLang = Set

-- Variants are given by a variability language in which nothing can be configured.
-- Every expressions describes a singleton set of variants.
-- 𝟙-Lang
data Variant : VarLang where
  Artifactᵥ : Artifactˡ Variant

data 𝟘-Lang : VarLang where

VariantSetoid : Size → Domain → Setoid 0ℓ 0ℓ
VariantSetoid i A = Eq.setoid (Variant i A)

IndexedVSet : Size → Domain → Set → Set
IndexedVSet i A I = Multiset I
  where open MSet (VariantSetoid i A) using (Multiset)

VSet : Domain → ℕ → Set
VSet A n = IndexedVSet ∞ A (Fin (suc n))

forget-last : ∀ {n : ℕ} {A : Set} → VSet A (suc n) → VSet A n
forget-last set x = set (Data.Fin.inject₁ x)
```

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → ConfLang → Set₁
Semantics L C = ∀ {i : Size} {A : Domain} → L i A → IndexedVSet ∞ A C
-- Semantics L C = ∀ {i j : Size} {A : Domain} → L i A → IndexedVSet (i ⊔ˢ j) A C
```

```agda
record VariabilityLanguage : Set₁ where
  field
    expression    : VarLang
    configuration : ConfLang
    semantics     : Semantics expression configuration
open VariabilityLanguage public

record Expression (A : Domain) (V : VariabilityLanguage) : Set₁ where
  field
    {size} : Size
    get : expression V size A
open Expression public

fromExpression : ∀ {i : Size} {A : Domain}
  → (L : VariabilityLanguage)
  → expression L i A
  → Expression A L
fromExpression {i} _ e = record
  { size = i
  ; get  = e
  }
```

## Helper Functions and Theorems

### Smart Constructors for Variants

```agda
leaf : ∀ {i : Size} {A : Set} → A → Variant (↑ i) A
leaf a = Artifactᵥ a []

leaves : ∀ {i : Size} {A : Set} → List A → List (Variant (↑ i) A)
leaves as = map leaf as
```

### Variant Equality

```agda
root-equality : ∀ {i : Size} {A : Set} {a b : A} {as bs : List (Variant i A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → a ≡ b
root-equality refl = refl

subtree-equality : ∀ {i : Size} {A : Set} {a b : A} {as bs : List (Variant i A)}
   → Artifactᵥ a as ≡ Artifactᵥ b bs
     ------------------------------
   → as ≡ bs
subtree-equality refl = refl

≡-dec : ∀ {i : Size} {A : Set} → DecidableEquality A → DecidableEquality (Variant i A)
≡-dec ≡-dec-A (Artifactᵥ a as) (Artifactᵥ b bs) with ≡-dec-A a b | ≡-dec-l (≡-dec ≡-dec-A) as bs
... | yes a≡b | yes as≡bs = yes (Eq.cong₂ Artifactᵥ a≡b as≡bs)
... | yes a≡b | no ¬as≡bs = no (¬as≡bs ∘ subtree-equality)
... | no ¬a≡b | _         = no (¬a≡b   ∘ root-equality)

equals : ∀ {i : Size} {A : Set} → DecidableEquality A → Variant i A → Variant i A → Bool
equals ≡-dec-A V W = isYes (≡-dec ≡-dec-A V W)
```

### Show

```agda
show-variant : ∀ {i : Size} {A : Set} → (A → String) → Variant i A → String
show-variant s (Artifactᵥ a []) = s a
show-variant s (Artifactᵥ a es@(_ ∷ _)) = s a ++ "-<" ++ (intersperse ", " (map (show-variant s) es)) ++ ">-"
```

### Misc

```agda
open import Data.List.NonEmpty using (List⁺)
open import Size using (↑_)
open import Util.Existence using (∃-Size; _,_)
open import Util.SizeJuggle

flip-VarLang : VarLang → Domain → Bounded
flip-VarLang L A i = L i A

forget-variant-size : ∀ {A : Domain} → ∃-Size[ i ] (Variant i A) → Variant ∞ A
forget-variant-size (i , v) = v

{-
Creates an Artifact from a list of expressions of a certain size.
The size of the resulting expression is larger by 1.
TODO: REMOVE WEAKENABLE.
-}
sequence-sized-artifact :
  ∀ {A : Domain}
    {L : VarLang}
  → Weaken (flip-VarLang L A)
  → Artifactˡ L
  → A
  → List⁺ (∃-Size[ i ] (L i A))
    ---------------------------
  → ∃-Size[ i ] (L i A)
sequence-sized-artifact {A} {L} w Artifact a cs =
  let max , es = unify-sizes⁺ w cs
   in
      ↑ max , Artifact a es
```

## Examples

```agda
module Examples where
  open import Data.String using (String)
  open Data.Fin using (zero; suc)

  vset-example : VSet ℕ 2
  vset-example zero = leaf 1
  vset-example (suc zero) = leaf 2
  vset-example (suc (suc zero)) = leaf 3
```
