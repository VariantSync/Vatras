module Framework.V2.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Function using (id; _∘_)
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
Feature Selection Language.
This is the semantic of an annotation language 𝔽. An instance of 𝕊 describes the
set of configurations for a feature language 𝔽.  Usually, each feature selection
language `S : 𝕊` has a some function `ConfigEvaluater F S Sel` which resolves an
expression of the annotation language `F : 𝔽` to a selection `Sel` interpreted
by a concrete language.
For example, a binary choice language may use `F → Bool` as the feature
selections language.
-}
𝕊 : Set₁
𝕊 = Set

ConfigEvaluator : 𝔽 → 𝕊 → Set → Set
ConfigEvaluator F S Sel = (S → F → Sel)

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
Moreover, constructs often denote variational expressions and hence require a language
for variability annotations 𝔽.
-}
-- ℂ : ∀ {ℓ} → Set (suc ℓ)
-- ℂ {ℓ} = 𝔼 {ℓ} → 𝔸 {ℓ} → Set ℓ
ℂ : Set₁
ℂ = 𝔼 → 𝔸 → Set

{-
Semantics of variability languages.
The semantics of a set of expressions `E : 𝔼` is a function
that configures a term `e : E A` to a variant `v : V A`
-}
𝔼-Semantics : 𝕍 → 𝕊 → 𝔼 → Set₁
𝔼-Semantics V S E =
  ∀ {A : 𝔸}
  → E A
  → S
  → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage (V : 𝕍) (S : 𝕊) : Set₁ where
  constructor syn_with-sem_
  field
    Expression : 𝔼
    Semantics  : 𝔼-Semantics V S Expression
open VariabilityLanguage public

-- Semantics of constructors
ℂ-Semantics : 𝕍 → 𝕊 → ℂ → Set₁
ℂ-Semantics V S C =
  ∀ {Sγ : 𝕊}
  → (Sγ → S) -- a function that lets us apply language configurations to constructs
  → {A : 𝔸} -- the domain in which we embed variability
  → (Γ : VariabilityLanguage V Sγ) -- The underlying language
  → C (Expression Γ) A -- the construct to compile
  → Sγ -- a configuration for underlying subexpressions
  → V A

record VariabilityConstruct (V : 𝕍) (S : 𝕊) : Set₁ where
  constructor con_with-sem_
  field
    -- how to create a constructor for a given language
    Construct : ℂ
    -- how to resolve a constructor for a given language
    construct-semantics : ℂ-Semantics V S Construct
  _⊢⟦_⟧ = construct-semantics {Sγ = S} id

-- Syntactic Containment
-- TODO: Is there any point in allowing a specialization of F here?
--       It lets us say "Construct x is in language y but only for the annotation language ℕ".
--       Is there ever a use case though, in which a language must be fixed to a particular annotation language?
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
record _⟦∈⟧_ {V S} (C : VariabilityConstruct V S) (Γ : VariabilityLanguage V S) : Set₁ where
  open VariabilityConstruct C
  private ⟦_⟧ = Semantics Γ
  field
    make : Construct ∈ₛ Expression Γ
    preservation : ∀ {A : 𝔸}
      → (c : Construct (Expression Γ) A)
      → ⟦ cons make c ⟧ ≗ construct-semantics id Γ c
open _⟦∈⟧_ public

_⟦∉⟧_ : ∀ {V S} → VariabilityConstruct V S → VariabilityLanguage V S → Set₁
C ⟦∉⟧ E = ¬ (C ⟦∈⟧ E)

_⟦⊆⟧_ :  ∀ {V S} → VariabilityLanguage V S → VariabilityLanguage V S → Set₁
_⟦⊆⟧_ {V} {S} E₁ E₂ = ∀ (C : VariabilityConstruct V S) → C ⟦∈⟧ E₁ → C ⟦∈⟧ E₂

_⟦≅⟧_ : ∀ {V S} → VariabilityLanguage V S → VariabilityLanguage V S → Set₁
E₁ ⟦≅⟧ E₂ = E₁ ⟦⊆⟧ E₂ × E₂ ⟦⊆⟧ E₁
