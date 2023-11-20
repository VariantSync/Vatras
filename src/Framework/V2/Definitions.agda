module Framework.V2.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Data.Unit using (⊤; tt) public
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
record VariabilityLanguage (V : 𝕍) : Set₁ where
  constructor Lang-⟪_,_,_⟫
  field
    Expression : 𝔼
    Config : 𝕊
    Semantics : 𝔼-Semantics V Config Expression
open VariabilityLanguage public

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


-- Constructors

record PlainConstruct : Set₁ where
  constructor Plain-⟪_,_⟫
  field
    PSyntax : ℂ

    {-|
    The semantics of a plain construct is a map.
    A plain construct does not embody any variational choices and does
    not require a configuration.
    Hence, after configuration, it just remains as is but any
    sub-expressions have been configured to variants.
    -}
    PSemantics : ∀ {V A}
      → (Γ : VariabilityLanguage V)
      → (e : PSyntax (Expression Γ) A)
      → (c : Config Γ)
      → PSyntax V A
open PlainConstruct public

Plain-ℂ-Semantics : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → (Γ : VariabilityLanguage V)
  → {A : 𝔸} -- the domain in which we embed variability
  → PSyntax P (Expression Γ) A -- the construct to compile
  → Config Γ -- a configuration for underlying subexpressions
  → V A
Plain-ℂ-Semantics P make Γ e = cons make ∘ PSemantics P Γ e

-- Semantics of constructors
Variational-ℂ-Semantics : 𝕍 → 𝕊 → ℂ → Set₁
Variational-ℂ-Semantics V S C =
  -- The underlying language, which the construct is part of.
  ∀ (Γ : VariabilityLanguage V)
  -- A function that lets us apply language configurations to constructs.
  -- A language might be composed many constructors, each requiring another type
  -- of configuration (i.e., each having different requirements on a configuration).
  -- To configure an expression, we thus need a configuration 'c : Config Γ', which
  -- satisfies _all_ these requirements.
  -- The function 'extract' fetches only those requirements from this big config
  -- that we need.
  → (extract : Config Γ → S)
  → {A : 𝔸} -- the domain in which we embed variability
  → C (Expression Γ) A -- the construct to compile
  → Config Γ -- a configuration for underlying subexpressions
  → V A

record VariabilityConstruct (V : 𝕍) : Set₁ where
  constructor Variational-⟪_,_,_⟫
  field
    -- How to create a constructor...
    VSyntax : ℂ
    -- What is required to configure a constructor...
    VConfig : 𝕊
    -- How to resolve a constructor...
    VSemantics : Variational-ℂ-Semantics V VConfig VSyntax
  -- _⊢⟦_⟧ = ∀ (Γ : VariabilityLanguage V) →  VSemantics Γ id
open VariabilityConstruct public

{-|
A variability construct C is compatible with a language Γ when the construct
can be used within Γ to configure expressions with that construct over that language.
This is the case when the configurations of the variability language Γ provide
enough information to configure a construct c : C.
A proof for compatibility is thus a function that extracts the necessary information
from a language's configuration.
TODO: We might want to have a better name for this.
-}
Compatible : ∀ {V} (C : VariabilityConstruct V) (Γ : VariabilityLanguage V) → Set
Compatible C Γ = Config Γ → VConfig C

-- Semantic containment of variational constructs
record _⟦∈⟧ᵥ_ {V} (C : VariabilityConstruct V) (Γ : VariabilityLanguage V) : Set₁ where
  private ⟦_⟧ = Semantics Γ
  field
    make : VSyntax C ∈ₛ Expression Γ
    extract : Compatible C Γ
    preservation : ∀ {A : 𝔸}
      → (c : VSyntax C (Expression Γ) A)
      → ⟦ cons make c ⟧ ≗ VSemantics C Γ extract c
open _⟦∈⟧ᵥ_ public

_⟦∉⟧ᵥ_ : ∀ {V} → VariabilityConstruct V → VariabilityLanguage V → Set₁
C ⟦∉⟧ᵥ E = ¬ (C ⟦∈⟧ᵥ E)

_⟦⊆⟧ᵥ_ :  ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦⊆⟧ᵥ E₂ = ∀ C → C ⟦∈⟧ᵥ E₁ → C ⟦∈⟧ᵥ E₂

_⟦≅⟧ᵥ_ : ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦≅⟧ᵥ E₂ = E₁ ⟦⊆⟧ᵥ E₂ × E₂ ⟦⊆⟧ᵥ E₁

-- Semantic containment of plain constructs
record _⟦∈⟧ₚ_ {V} (C : PlainConstruct)  (Γ : VariabilityLanguage V) : Set₁ where
  private ⟦_⟧ = Semantics Γ
  field
    C∈ₛΓ : PSyntax C ∈ₛ Expression Γ
    C∈ₛV : PSyntax C ∈ₛ V
    -- Commuting Square:
    -- Creating a plain construct 'const P∈ₛΓ' in a variability language Γ and then configuring the expression
    -- should be equivalent to
    -- configuring the expression first and then creating the plain construct in the variant.
    -- This equality ensures that plain constructs are resistant to configuration.
    resistant : ∀ {A} (c : PSyntax C (Expression Γ) A)
      → Semantics Γ (cons C∈ₛΓ c) ≗ cons C∈ₛV ∘ PSemantics C Γ c
open _⟦∈⟧ₚ_ public

_⟦∉⟧ₚ_ : ∀ {V} → PlainConstruct → VariabilityLanguage V → Set₁
C ⟦∉⟧ₚ E = ¬ (C ⟦∈⟧ₚ E)

_⟦⊆⟧ₚ_ :  ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦⊆⟧ₚ E₂ = ∀ C → C ⟦∈⟧ₚ E₁ → C ⟦∈⟧ₚ E₂

_⟦≅⟧ₚ_ : ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦≅⟧ₚ E₂ = E₁ ⟦⊆⟧ₚ E₂ × E₂ ⟦⊆⟧ₚ E₁

---- Plain constructs can be seen as variational constructs that do nothing upon configuration. ---

Plain-ℂ-Semantics-Are-Variational-ℂ-Semantics : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → Variational-ℂ-Semantics V ⊤ (PSyntax P)
Plain-ℂ-Semantics-Are-Variational-ℂ-Semantics P make Γ _ e = Plain-ℂ-Semantics P make Γ e

toVariational : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → VariabilityConstruct V
toVariational P make = Variational-⟪ PSyntax P , ⊤ , Plain-ℂ-Semantics-Are-Variational-ℂ-Semantics P make ⟫

⟦∈⟧ₚ→⟦∈⟧ᵥ : ∀ {V P} {Γ : VariabilityLanguage V}
  → (p : P ⟦∈⟧ₚ Γ)
  → toVariational P (C∈ₛV p) ⟦∈⟧ᵥ Γ
⟦∈⟧ₚ→⟦∈⟧ᵥ P⟦∈⟧ₚΓ = record
  { make = C∈ₛΓ P⟦∈⟧ₚΓ
  ; extract = λ _ → tt
  ; preservation = resistant P⟦∈⟧ₚΓ
  }
