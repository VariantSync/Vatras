```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Framework.Definitions where
```

# Definitions of Central Abstractions for Variability Languages

```agda
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-l)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _++_; intersperse)
open import Data.Product using (_×_; ∃-syntax; _,_)

open import Function using (_∘_)
open import Level using (0ℓ) renaming (suc to ℓ-suc)
open import Size using (Size; ↑_; _⊔ˢ_; ∞)

open import Relation.Nullary.Decidable using (Dec; yes; no; isYes; False; toWitnessFalse)
open import Relation.Binary using (Setoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)

import Data.IndexedSet as ISet
open import Util.Existence using (∃-Size)
```

This module contains the central definitions of our framework (Section 4).

We model variability languages as embedded domain specific languages. That is, each variability language is described by a type `L i A : 𝕃`, where `i` is a size used for termination checking, and `A : 𝔸` is a set of atoms that represents the domain we are making variational.
A set of atoms can represent for example text or source code implemented by the type `String` or some AST of a programming language.
Each variability language `𝕃` is also parameterized in a size which is irrelevant for studying variation but we need it to ensure that our proofs terminate.
```agda
{-| Type of atom sets -}
𝔸 : Set₁
𝔸 = Set

{-| Type of variability languages -}
𝕃 : Set₁
𝕃 = Size → 𝔸 → Set

{-| Type of configuration languages -}
ℂ : Set₁
ℂ = Set
```

Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
```agda
Artifactˡ : 𝕃 → Set₁
Artifactˡ L = ∀ {i : Size} {A : 𝔸} → A → List (L i A) → L (↑ i) A
```

Variability languages denote sets of variants.
Interestingly, variants can be modelled as a variability language in which nothing can be configured.
Every expressions describes a singleton set of variants.
```agda
-- 𝟙-Lang
data Variant : 𝕃 where
  Artifactᵥ : Artifactˡ Variant

-- Empty variability language
data 𝟘-Lang : 𝕃 where
```

Because we will frequently have to compare variants based on propositional equivalence, we create an alias.
```agda
VariantSetoid : Size → 𝔸 → Setoid 0ℓ 0ℓ
VariantSetoid i A = Eq.setoid (Variant i A)
```

The semantic domain of variability languages is given by a finite, non-empty indexed set of variants.
It is an indexed set because two different configurations might yield the same variant (e.g., if there is an unused feature, or toggling a certain feature has no effect because all of its atoms already dead based on another selection).
```agda
IndexedVMap : Size → 𝔸 → Set → Set
IndexedVMap i A I = IndexedSet I
  where open ISet (VariantSetoid i A) using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : 𝔸 → ℕ → Set
VMap A n = IndexedVMap ∞ A (Fin (suc n))

-- Utility functions for manipulating variant maps.
forget-first : ∀ {n : ℕ} {A : 𝔸} → VMap A (suc n) → VMap A n
forget-first set i = set (Data.Fin.suc i)

forget-last : ∀ {n : ℕ} {A : 𝔸} → VMap A (suc n) → VMap A n
forget-last set i = set (Data.Fin.inject₁ i)

forget-all : ∀ {n : ℕ} {A : Set} → VMap A n → VMap A zero
forget-all {zero}  set = set
forget-all {suc _} set = forget-all (forget-last set)
```

The semantics of a language `L i A : 𝕃` and its corresponding configuration language `C : ℂ` is a function that configures an expression to a variant:
```agda
Semantics : 𝕃 → ℂ → Set₁
Semantics L C = ∀ {i : Size} {A : 𝔸} → L i A → IndexedVMap ∞ A C
```

We further introduce convenience records that gather all relevant information to characterize a single language.
```agda
record VariabilityLanguage : Set₁ where
  field
    expression    : 𝕃 -- unfortunately, "syntax" is a keyword in Agda so we cannot use that as field name
    configuration : ℂ
    semantics     : Semantics expression configuration
open VariabilityLanguage public

record Expression (A : 𝔸) (V : VariabilityLanguage) : Set₁ where
  constructor [_]
  field
    {size} : Size
    get : expression V size A
open Expression public

fromExpression : ∀ {i : Size} {A : 𝔸}
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

flip-𝕃 : 𝕃 → 𝔸 → Bounded
flip-𝕃 L A i = L i A

suc-variant-size : ∀ {i} {A} → Variant i A → Variant i A
suc-variant-size v = v

forget-variant-size : ∀ {i} {A} → Variant i A → Variant ∞ A
forget-variant-size (Artifactᵥ a []) = Artifactᵥ a []
forget-variant-size (Artifactᵥ a (e ∷ es)) = Artifactᵥ a (map forget-variant-size (e ∷ es))

forget-size-cong : ∀ {i} {A B : Set} {x : Variant ∞ A} {y : Variant i A}
  → (f : ∀ {j} → Variant j A → B)
  → x ≡ forget-variant-size y
  → f x ≡ f (forget-variant-size y)
forget-size-cong _ refl = refl

sequence-forget-size : ∀ {A} {i} {a : A}
  → (xs : List (Variant i A))
  → Artifactᵥ a (map forget-variant-size xs) ≡ forget-variant-size (Artifactᵥ a xs)
sequence-forget-size [] = refl
sequence-forget-size (_ ∷ _) = refl

{-
Creates an Artifact from a list of expressions of a certain size.
The size of the resulting expression is larger by 1.
TODO: REMOVE WEAKENABLE.
-}
sequence-sized-artifact :
  ∀ {A : 𝔸}
    {L : 𝕃}
  → Weaken (flip-𝕃 L A)
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

  vmap-example : VMap ℕ 2
  vmap-example zero = leaf 1
  vmap-example (suc zero) = leaf 2
  vmap-example (suc (suc zero)) = leaf 3
```
