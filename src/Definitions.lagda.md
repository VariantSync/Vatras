```agda
{-# OPTIONS --sized-types #-}

module Definitions where
```

# Definitions of Central Abstractions for Variability Languages

```agda
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Size using (Size; ↑_)
open import SemanticDomain using (Variant; leaf)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
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
VSet : FeatureLang → SelectionLang → Domain → Set
VSet F S A = Multiset (Configuration F S)
  where open import Data.Multiset (Variant A) Eq.isEquivalence using (Multiset)
```

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → FeatureLang → SelectionLang → Set₁
Semantics L F S = ∀ {i : Size} {A : Domain} → L i A → VSet F S A
```

```agda
record VariabilityLanguage : Set₁ where
  field
    vLang : VarLang
    fLang : FeatureLang
    sLang : SelectionLang
    semantics : Semantics vLang fLang sLang
open VariabilityLanguage public

record Expression (A : Domain) (V : VariabilityLanguage) : Set₁ where
  field
    {size} : Size
    get : vLang V size A
open Expression public

fromExpression : ∀ {i : Size} {A : Domain} {L : VariabilityLanguage} → vLang L i A → Expression A L
fromExpression e = record { get = e }
```


Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
```agda
Artifactˡ : VarLang → Set₁
Artifactˡ L = ∀ {i : Size} {A : Domain} → A → List (L i A) → L (↑ i) A
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


## Helper Functions and Theorems

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
