module Framework.V2.Construct where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Data.Unit using (⊤; tt) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Function using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.VariabilityLanguage
open import Framework.V2.ConfigurationLanguage
open import Framework.V2.FunctionLanguage

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

record PlainConstruct : Set₁ where
  constructor Plain-⟪_,_⟫
  field
    PSyntax : ℂ

    {-|
    The semantics of a plain construct is a congruence rule (i.e., a functorial map in this case).
    A plain construct does not embody any variational choices and does not require a configuration.
    Hence, after configuration, it just remains as is but any
    sub-expressions are configured to variants.
    -}
    pcong : ∀ {V A}
      → (Γ : VariabilityLanguage V)
      → (e : PSyntax (Expression Γ) A)
      → (c : Config Γ)
      → PSyntax V A
open PlainConstruct public

PlainConstruct-Semantics : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → (Γ : VariabilityLanguage V)
  → {A : 𝔸} -- the domain in which we embed variability
  → PSyntax P (Expression Γ) A -- the construct to compile
  → Config Γ -- a configuration for underlying subexpressions
  → V A
PlainConstruct-Semantics P make Γ e = cons make ∘ pcong P Γ e

VariationalConstruct-Semantics : 𝕍 → 𝕂 → ℂ → Set₁
VariationalConstruct-Semantics V K C =
  -- The underlying language, which the construct is part of.
  ∀ (Γ : VariabilityLanguage V)
  -- A function that lets us apply language configurations to constructs.
  -- A language might be composed many constructors, each requiring another type
  -- of configuration (i.e., each having different requirements on a configuration).
  -- To configure an expression, we thus need a configuration 'c : Config Γ', which
  -- satisfies _all_ these requirements.
  -- The function 'extract' fetches only those requirements from this big config
  -- that we need.
  → (extract : Config Γ → K)
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
    VConfig : 𝕂
    -- How to resolve a constructor...
    VSemantics : VariationalConstruct-Semantics V VConfig VSyntax
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
Compatible C Γ = Config Γ ⇒ VConfig C

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
      → Semantics Γ (cons C∈ₛΓ c) ≗ cons C∈ₛV ∘ pcong C Γ c
open _⟦∈⟧ₚ_ public

_⟦∉⟧ₚ_ : ∀ {V} → PlainConstruct → VariabilityLanguage V → Set₁
C ⟦∉⟧ₚ E = ¬ (C ⟦∈⟧ₚ E)

_⟦⊆⟧ₚ_ :  ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦⊆⟧ₚ E₂ = ∀ C → C ⟦∈⟧ₚ E₁ → C ⟦∈⟧ₚ E₂

_⟦≅⟧ₚ_ : ∀ {V} → VariabilityLanguage V → VariabilityLanguage V → Set₁
E₁ ⟦≅⟧ₚ E₂ = E₁ ⟦⊆⟧ₚ E₂ × E₂ ⟦⊆⟧ₚ E₁

---- Plain constructs can be seen as variational constructs that do nothing upon configuration. ---

PlainConstruct-Semantics-Are-VariationalConstruct-Semantics : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → VariationalConstruct-Semantics V ⊤ (PSyntax P)
PlainConstruct-Semantics-Are-VariationalConstruct-Semantics P make Γ _ e
  = PlainConstruct-Semantics P make Γ e

{-|
All plain constructs are also variational constructs
(but they have no impact on the configuration process.)
-}
toVariational : ∀ {V}
  → (P : PlainConstruct)
  → PSyntax P ∈ₛ V
  → VariabilityConstruct V
toVariational P make = Variational-⟪ PSyntax P , ⊤ , PlainConstruct-Semantics-Are-VariationalConstruct-Semantics P make ⟫

⟦∈⟧ₚ→⟦∈⟧ᵥ : ∀ {V P} {Γ : VariabilityLanguage V}
  → (p : P ⟦∈⟧ₚ Γ)
  → toVariational P (C∈ₛV p) ⟦∈⟧ᵥ Γ
⟦∈⟧ₚ→⟦∈⟧ᵥ P⟦∈⟧ₚΓ = record
  { make = C∈ₛΓ P⟦∈⟧ₚΓ
  ; extract = λ _ → tt
  ; preservation = resistant P⟦∈⟧ₚΓ
  }
