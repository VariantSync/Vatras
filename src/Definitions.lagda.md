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
open import Data.Product using (_×_; _,_)
open import Size using (Size; ↑_; ∞)
-- open import SemanticDomain using (Variant; leaf)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; isYes; False; toWitnessFalse)

open import Function using (_∘_)
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
FeatureLang : Set₁
FeatureLang = Set

SelectionLang : Set₁
SelectionLang = Set

Assignment : FeatureLang → SelectionLang → Set
Assignment = _×_

Configuration : FeatureLang → SelectionLang → Set
Configuration A S = List (Assignment A S)

infix 4 _∈_
data _∈_ {F : FeatureLang} {S : SelectionLang} : Assignment F S → Configuration F S → Set where
   here : ∀ {f : F} {s : S} {as}
       ----------------------
     → (f , s) ∈ (f , s) ∷ as

   there : ∀ {f f' : F} {s s' : S} {as}
     → f ≢ f'
     → (f , s) ∈ as
       ------------------------
     → (f , s) ∈ (f' , s') ∷ as

-- -- Smart constructor for there that will make Agda
-- -- figure out the proof. This is still magic to me.
-- there' : ∀ {A S : Set} {a a' : A} {s s' : S} {as}
--   → {a≢a' : False (a ≟ a')}
--   → (a , s) ∈ as
--     ---------------------
--   → (a , s) ∈ (a' , s') ∷ as
-- there' {a≢a' = a≢a'} = there (toWitnessFalse a≢a')
```

```agda
-- data Variant (A : Set) : Set where
--   Artifactᵥ : A → List (Variant A) → Variant A

open import Relation.Binary using (Setoid)
open import Level using (0ℓ; suc)
import Relation.Binary.PropositionalEquality as Eq

-- Variants are given by a variability language in which nothing can be configured.
-- Every expressions describes a singleton set of variants.
-- 𝟙-Lang
data Variant : VarLang where
  Artifactᵥ : Artifactˡ Variant

data 𝟘-Lang : VarLang where

VariantSetoid : Domain → Setoid 0ℓ 0ℓ
VariantSetoid A = Eq.setoid (Variant ∞ A)

VSet : FeatureLang → SelectionLang → Domain → Set
VSet F S A = Multiset (Configuration F S)
  where open import Data.Multiset (VariantSetoid A) using (Multiset)

-- open import Data.List.Relation.Unary.All using (All; reduce; []; _∷_)

-- We cannot use this predicate because there is no guarantee that mkArtifact indeed produces variants.
-- We cannot constrain mkArtifact to be a constructor, and thus it could be a function that creates
-- non-artifact expressions.
-- data IsVariant {A : Domain} {L : VarLang} : ∀ {i : Size} → L i A → Set₁ where
--   V-Leaf : ∀ {a : A} {mkArtifact : Artifactˡ L}
--       ---------------------------
--     → IsVariant (mkArtifact a [])

--   V-Node : ∀ {i : Size} {a : A} {mkArtifact : Artifactˡ L} {as : List (L i A)}
--     → All (λ e → IsVariant {A} {L} e) as
--       ----------------------------------
--     → IsVariant (mkArtifact a as)
```

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → FeatureLang → SelectionLang → Set₁
Semantics L F S = ∀ {i : Size} {A : Domain} → L i A → VSet F S A
```

```agda
record VariabilityLanguage : Set₁ where
  field
    expression : VarLang
    fLang : FeatureLang
    sLang : SelectionLang
    semantics : Semantics expression fLang sLang
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
fromExpression _ e = record { get = e }

open import Function.Inverse using (Inverse; _↔_)
open import Data.Product using (Σ-syntax)


--VSet F S A
-- FullyConfigured : ∀ {A : Domain} {L : VariabilityLanguage}
--   → (e : Expression A L)
--   → Set
-- FullyConfigured {A} {L} e = Σ[ v ∈ Variant A ] (e ↔ v)
--   where F = fLang L
--         S = sLang L


-- the index should be configurations!!!
-- record VSet (A : Set) : Set where
--   constructor _/_
--   field
--     size-1 : ℕ
--     pick : Multiset (Fin (suc size-1)) (Variant A)
-- open VSet public



-- We did not equip variants with bounds yet so we just assume the following functions to terminate.

-- ## Equality



-- module Examples where
--   open import Data.Fin using (Fin; suc; zero)
--   open import Data.Nat using (ℕ)

--   vset-example : VSet 2 ℕ
--   vset-example zero = leaf 1
--   vset-example (suc zero) = leaf 2
--   vset-example (suc (suc zero)) = leaf 2 -- multiset possible because injectivity is not required

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
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ)
  open import Data.String using (String)
  open Data.List using ([]; _∷_)

  vset-example : ∀ {F : FeatureLang} {S : SelectionLang} → VSet F S ℕ
  vset-example [] = leaf 1
  vset-example (a ∷ []) = leaf 2
  vset-example (a ∷ b ∷ as) = leaf 3
```
