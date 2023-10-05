module Framework.V2.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Negation using (¬_)

-- open import Level using (suc; _⊔_)

{-
Some Atomic Data.
We have no assumptions on that data so its just a type.
-}
-- 𝔸 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔸 {ℓ} = Set ℓ
𝔸 : Set₁
𝔸 = Set

{-
Variant Language.
A variant should represent atomic data in some way so its parameterized in atomic data.
-}
-- 𝕍 : ∀ {ℓ} → Set (suc ℓ)
-- 𝕍 {ℓ} = 𝔸 {ℓ} → Set ℓ
𝕍 : Set₁
𝕍 = 𝔸 → Set

{-
Annotation Language.
This can be names or propositional formulas or whatever you like to annotate artifacts with.
We have no assumptions on this kind of language (yet).
In the future, it might be interesting to dig deeper into 𝔽 and to explore its impact on a
language's expressiveness more deeply.
-}
-- 𝔽 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔽 {ℓ} = Set ℓ
𝔽 : Set₁
𝔽 = Set

{-
Selections Language.
This is the semantic domain of an annotation language 𝔽.
Resolving an annotation `F : 𝔽` yields some data `S : 𝕊` which
can be used to decide whether to in- or exclude an annotated statement
(i.e., for options) or to decide which alternative to pick from a range of
annotated elements (i.e., for choices).
Basically, this can be any kind of information as long as the semantics of
a construct can resolve it.
-}
-- 𝕊 : ∀ {ℓ} → Set (suc ℓ)
-- 𝕊 {ℓ} = Set ℓ
𝕊 : Set₁
𝕊 = Set

{-
The set of expressions of a variability language.
An expression denotes a set of variants and hence, variant-like sub-terms
occur within an expression.
Such sub-terms describe variants of atomic data (i.e., some structure on atomic elements),
and hence expressions are parameterized in the type of this atomic data.
-}
-- 𝔼 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔼 {ℓ} = 𝔸 {ℓ} → Set ℓ
𝔼 : Set₁
𝔼 = 𝔸 → Set

{-
Variability Construct.
A variability language is composed from a set of constructs (i.e., grammar rules).
Each construct may recursively contain further expressions (made up from constructs again).
Thus, constructs must know the overall set of expressions to include.
Moreover, constructs might directly host some atomic data (e.g., leaf nodes) and hence
they must know the atomic data type.
-}
-- ℂ : ∀ {ℓ} → Set (suc ℓ)
-- ℂ {ℓ} = 𝔼 {ℓ} → 𝔸 {ℓ} → Set ℓ
ℂ : Set₁
ℂ = 𝔼 → 𝔸 → Set

{-
Configurations.
A configuration is anything that allows us to do resolve an annotation `F : 𝔽`
to a selection `S : 𝕊`, which in turn gets resolved by language and construct semantics.
-}
-- Config : ∀ {ℓ₁ ℓ₂} → (F : 𝔽 {ℓ₁}) (S : 𝕊 {ℓ₂}) → Set (ℓ₁ ⊔ ℓ₂)
Config : 𝔽 → 𝕊 → Set
Config F S = F → S

{-
Semantics of variability languages.
The semantics of a set of expressions `E : 𝔼` is a function
that configures a term `e : E A` to a variant `v : V A`
-}
𝔼-Semantics : 𝕍 → 𝔽 → 𝕊 → 𝔼 → Set₁
𝔼-Semantics V F S E =
  ∀ {A : 𝔸}
  → E A
  → Config F S
  → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  constructor _with-sem_
  field
    expression-set : 𝔼
    semantics      : 𝔼-Semantics V F S expression-set
open VariabilityLanguage public

-- Semantics of constructors
ℂ-Semantics : 𝕍 → 𝔽 → 𝕊 → ℂ → Set₁
ℂ-Semantics V F S C =
  ∀ {A : 𝔸}
  → (Γ : VariabilityLanguage V F S)
  → C (expression-set Γ) A
  → Config F S
  → V A

record VariabilityConstruct (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  field
    -- how to create a constructor for a given language
    construct : ℂ
    -- how to resolve a constructor for a given language
    semantics : ℂ-Semantics V F S construct
open VariabilityConstruct public

-- Syntactic Containment
record _∈ₛ_ (C : ℂ) (E : 𝔼) : Set₁ where
  field
    -- from a construct, an expression can be created
    cons : ∀ {A} → C E A → E A
    -- an expression might be the construct C
    snoc : ∀ {A} →   E A → Maybe (C E A)
    -- An expression of a construct must preserve all information of that construct.
    -- There might be more syntactic information though because of which we do not require
    -- the dual equality cons ∘ snoc
    id-l : ∀ {A} → snoc {A} ∘ cons {A} ≗ just
open _∈ₛ_ public

_∉ₛ_ : ℂ → 𝔼 → Set₁
C ∉ₛ E = ¬ (C ∈ₛ E)

_⊆ₛ_ : 𝔼 → 𝔼 → Set₁
E₁ ⊆ₛ E₂ = ∀ (C : ℂ) → C ∈ₛ E₁ → C ∈ₛ E₂

_≅ₛ_ : 𝔼 → 𝔼 → Set₁
E₁ ≅ₛ E₂ = E₁ ⊆ₛ E₂ × E₂ ⊆ₛ E₁

-- Semantic Containment
record _⟦∈⟧_ {V F S} (R : VariabilityConstruct V F S) (Γ : VariabilityLanguage V F S) : Set₁ where
  private
    E = expression-set Γ
    C = construct R

  field
    make : C ∈ₛ E
    preservation : ∀ {A : 𝔸} → (c : C E A) → semantics Γ (cons make c) ≗ semantics R Γ c
open _⟦∈⟧_ public

_⟦∉⟧_ : ∀ {V F S} → VariabilityConstruct V F S → VariabilityLanguage V F S → Set₁
C ⟦∉⟧ E = ¬ (C ⟦∈⟧ E)

_⟦⊆⟧_ :  ∀ {V F S} → VariabilityLanguage V F S → VariabilityLanguage V F S → Set₁
_⟦⊆⟧_ {V} {F} {S} E₁ E₂ = ∀ (C : VariabilityConstruct V F S) → C ⟦∈⟧ E₁ → C ⟦∈⟧ E₂

_⟦≅⟧_ : ∀ {V F S} → VariabilityLanguage V F S → VariabilityLanguage V F S → Set₁
E₁ ⟦≅⟧ E₂ = E₁ ⟦⊆⟧ E₂ × E₂ ⟦⊆⟧ E₁
