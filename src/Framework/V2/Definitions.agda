module Framework.V2.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Level using (suc; _⊔_; Setω)

{-
Some Atomic Data.
We have no assumptions on that data so its just a type.
-}
𝔸 : ∀ ℓ → Set (suc ℓ)
𝔸 ℓ = Set ℓ
-- 𝔸 : Set₁
-- 𝔸 = Set

{-
Variant Language.
A variant should represent atomic data in some way so its parameterized in atomic data.
-}
𝕍 : ∀ ℓ → Set (suc ℓ)
𝕍 ℓ = 𝔸 ℓ → Set ℓ
-- 𝕍 : Set₁
-- 𝕍 = 𝔸 → Set

{-
Annotation Language.
This can be names or propositional formulas or whatever you like to annotate artifacts with.
We have no assumptions on this kind of language (yet).
In the future, it might be interesting to dig deeper into 𝔽 and to explore its impact on a
language's expressiveness more deeply.
-}
𝔽 : ∀ ℓ → Set (suc ℓ)
𝔽 ℓ = Set ℓ
-- 𝔽 : Set₁
-- 𝔽 = Set

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
𝕊 : ∀ ℓ → Set (suc ℓ)
𝕊 ℓ = Set ℓ
-- 𝕊 : Set₁
-- 𝕊 = Set

{-
The set of expressions of a variability language.
An expression denotes a set of variants and hence, variant-like sub-terms
occur within an expression.
Such sub-terms describe variants of atomic data (i.e., some structure on atomic elements),
and hence expressions are parameterized in the type of this atomic data.
-}
𝔼 : ∀ ℓ → Set (suc ℓ)
𝔼 ℓ = 𝔸 ℓ → Set ℓ
-- 𝔼 : Set₁
-- 𝔼 = 𝔸 → Set

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
ℂ : ∀ ℓ ℓᶠ → Set (suc (ℓ ⊔ ℓᶠ))
ℂ ℓ ℓᶠ = 𝔽 ℓᶠ → 𝔼 ℓ → 𝔸 ℓ → Set (ℓ ⊔ ℓᶠ)
-- ℂ : Set₁
-- ℂ = 𝔽 → 𝔼 → 𝔸 → Set

{-
Configurations.
A configuration is anything that allows us to do resolve an annotation `F : 𝔽`
to a selection `S : 𝕊`, which in turn gets resolved by language and construct semantics.
-}
-- Config : ∀ {ℓ₁ ℓ₂} → (F : 𝔽 {ℓ₁}) (S : 𝕊 {ℓ₂}) → Set (ℓ₁ ⊔ ℓ₂)
Config : ∀ {ℓ₁ ℓ₂} → 𝔽 ℓ₁ → 𝕊 ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
Config F S = F → S

{-
Semantics of variability languages.
The semantics of a set of expressions `E : 𝔼` is a function
that configures a term `e : E A` to a variant `v : V A`
-}
𝔼-Semantics : ∀ {ℓ ℓᶠ ℓˢ} → 𝕍 ℓ → 𝔽 ℓᶠ → 𝕊 ℓˢ → 𝔼 ℓ → Set (suc ℓ ⊔ ℓᶠ ⊔ ℓˢ)
𝔼-Semantics {ℓ} V F S E =
  ∀ {A : 𝔸 ℓ}
  → E A
  → Config F S
  → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage {ℓ ℓᶠ ℓˢ} (V : 𝕍 ℓ) (F : 𝔽 ℓᶠ) (S : 𝕊 ℓˢ) : Set (suc ℓ ⊔ ℓᶠ ⊔ ℓˢ) where
  constructor syn_with-sem_
  field
    Expression : 𝔼 ℓ
    Semantics  : 𝔼-Semantics V F S Expression
open VariabilityLanguage public

-- Semantics of constructors
ℂ-Semantics : ∀ {ℓ ℓᶠ ℓˢ} → 𝕍 ℓ → 𝔽 ℓᶠ → 𝕊 ℓˢ → ℂ ℓ ℓᶠ → Setω
ℂ-Semantics {ℓ} V F S C =
  ∀ {ℓᶠ' ℓˢ'} {Fγ : 𝔽 ℓᶠ'} {Sγ : 𝕊 ℓˢ'}
  → (Config Fγ Sγ → Config F S) -- a function that lets us apply language configurations to constructs
  → {A : 𝔸 ℓ} -- the domain in which we embed variability
  → (Γ : VariabilityLanguage V Fγ Sγ) -- The underlying language
  → C F (Expression Γ) A -- the construct to compile
  → Config Fγ Sγ -- a configuration for underlying subexpressions
  → V A

record VariabilityConstruct {ℓ ℓᶠ ℓˢ} (V : 𝕍 ℓ) (F : 𝔽 ℓᶠ) (S : 𝕊 ℓˢ) : Setω where
  constructor con_with-sem_
  field
    -- how to create a constructor for a given language
    Construct : ℂ ℓ ℓᶠ
    -- how to resolve a constructor for a given language
    construct-semantics : ℂ-Semantics V F S Construct
  _⊢⟦_⟧ = construct-semantics id

-- Syntactic Containment
-- TODO: Is there any point in allowing a specialization of F here?
--       It lets us say "Construct x is in language y but only for the annotation language ℕ".
--       Is there ever a use case though, in which a language must be fixed to a particular annotation language?
record _⊢_∈ₛ_ {ℓ ℓᶠ} (F : 𝔽 ℓᶠ) (C : ℂ ℓ ℓᶠ) (E : 𝔼 ℓ) : Set (suc ℓ ⊔ ℓᶠ) where
  field
    -- from a construct, an expression can be created
    cons : ∀ {A} → C F E A → E A
    -- an expression might be the construct C
    snoc : ∀ {A} →   E A → Maybe (C F E A)
    -- An expression of a construct must preserve all information of that construct.
    -- There might be more syntactic information though because of which we do not require
    -- the dual equality cons ∘ snoc
    id-l : ∀ {A} → snoc {A} ∘ cons {A} ≗ just
open _⊢_∈ₛ_ public

_⊢_∉ₛ_ : ∀ {ℓ ℓᶠ} → 𝔽 ℓᶠ → ℂ ℓ ℓᶠ → 𝔼 ℓ → Set (suc ℓ ⊔ ℓᶠ)
F ⊢ C ∉ₛ E = ¬ (F ⊢ C ∈ₛ E)

_⊢_⊆ₛ_ : ∀ {ℓ ℓᶠ} → 𝔽 ℓᶠ → 𝔼 ℓ → 𝔼 ℓ → Set (suc ℓ ⊔ suc ℓᶠ)
_⊢_⊆ₛ_ {ℓ} {ℓᶠ} F E₁ E₂ = ∀ (C : ℂ ℓ ℓᶠ) → F ⊢ C ∈ₛ E₁ → F ⊢ C ∈ₛ E₂

_⊢_≅ₛ_ : ∀ {ℓ ℓᶠ} → 𝔽 ℓᶠ → 𝔼 ℓ → 𝔼 ℓ → Set (suc ℓ ⊔ suc ℓᶠ)
F ⊢ E₁ ≅ₛ E₂ = F ⊢ E₁ ⊆ₛ E₂ × F ⊢ E₂ ⊆ₛ E₁

-- Semantic Containment
record _⟦∈⟧_ {ℓ ℓᶠ ℓˢ} {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ} (C : VariabilityConstruct V F S) (Γ : VariabilityLanguage V F S) : Set (suc ℓ ⊔ ℓᶠ ⊔ ℓˢ) where
  open VariabilityConstruct C
  private ⟦_⟧ = Semantics Γ
  field
    make : F ⊢ Construct ∈ₛ Expression Γ
    preservation : ∀ {A : 𝔸 ℓ}
      → (c : Construct F (Expression Γ) A)
      → ⟦ cons make c ⟧ ≗ construct-semantics id Γ c
open _⟦∈⟧_ public

_⟦∉⟧_ : ∀ {ℓ ℓᶠ ℓˢ} {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ} → VariabilityConstruct V F S → VariabilityLanguage V F S → Set (suc ℓ ⊔ ℓᶠ ⊔ ℓˢ)
C ⟦∉⟧ E = ¬ (C ⟦∈⟧ E)

_⟦⊆⟧_ :  ∀ {ℓ ℓᶠ ℓˢ} {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ} → VariabilityLanguage V F S → VariabilityLanguage V F S → Setω
_⟦⊆⟧_ {V = V} {F = F} {S = S} E₁ E₂ = ∀ (C : VariabilityConstruct V F S) → C ⟦∈⟧ E₁ → C ⟦∈⟧ E₂

record _⟦≅⟧_ {ℓ ℓᶠ ℓˢ} {V : 𝕍 ℓ} {F : 𝔽 ℓᶠ} {S : 𝕊 ℓˢ} (E₁ E₂ : VariabilityLanguage V F S) : Setω where
  field
    left  : E₁ ⟦⊆⟧ E₂
    right : E₂ ⟦⊆⟧ E₁
