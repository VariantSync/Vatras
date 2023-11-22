module Framework.V2.Config where

open import Data.Product using (_,_; _×_; Σ; Σ-syntax)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Binary using (Rel)
open import Relation.Nullary.Negation using (¬_)
open import Function using (_∘_; id; Injective)
open import Level using (0ℓ)

-- The syntax of a configuration language.
𝕂 : Set₁
𝕂 = Set

_⇒ᵏ_ : 𝕂 → 𝕂 → Set
A ⇒ᵏ B = A → B

record _⇔ᵏ_ (A B : 𝕂) : Set where
  field
    to   : A → B
    from : B → A
open _⇔ᵏ_ public

-- The semantics of a configuration language
-- This semantics is of the same form as for variability languages : Expression → Config → Variant
-- So all of the following to compare configurations is exactly very similar.
-- Very often though, 𝕂-Sem will just be 'id' because we often model a configuration directly
-- as a function. In some circumstances though, this is not possible.
𝕂-Sem : 𝕂 → (I : Set) → (O : Set) → Set
𝕂-Sem K I O = K → (I → O)

record ConfigurationLanguage (I O : Set) : Set₁ where
  constructor Conf-⟪_,_⟫
  field
    CSyntax : 𝕂
    CSemantics : 𝕂-Sem CSyntax I O
open ConfigurationLanguage public

_,_⊢_⊆ᵏ_ :
  ∀ {O I J}
  → (K₁ : ConfigurationLanguage I O)
  → (K₂ : ConfigurationLanguage J O)
  → CSyntax K₁
  → CSyntax K₂
  → Set
_,_⊢_⊆ᵏ_ {O} K₁ K₂ k₁ k₂ = ⟦ k₁ ⟧₁ ⊆ ⟦ k₂ ⟧₂
  where
    ⟦_⟧₁ = CSemantics K₁
    ⟦_⟧₂ = CSemantics K₂
    open import Data.IndexedSet (Eq.setoid O)

-- semantic equivalence
_,_⊢_≅ᵏ_ :
  ∀ {O I J}
  → (K₁ : ConfigurationLanguage I O)
  → (K₂ : ConfigurationLanguage J O)
  → CSyntax K₁
  → CSyntax K₂
  → Set
_,_⊢_≅ᵏ_ {O} K₁ K₂ k₁ k₂ = ⟦ k₁ ⟧₁ ≅ ⟦ k₂ ⟧₂
  where
    ⟦_⟧₁ = CSemantics K₁
    ⟦_⟧₂ = CSemantics K₂
    open import Data.IndexedSet (Eq.setoid O)

SemanticsPreserving :
  ∀ {I O}
  → (K₁ K₂ : ConfigurationLanguage I O)
  → CSyntax K₁ ⇒ᵏ CSyntax K₂
  → Set
SemanticsPreserving K₁ K₂ t = ∀ (c : CSyntax K₁) → K₁ , K₂ ⊢ c ≅ᵏ t c

-- Now the fun begins when we want to compare configurations with different input languages.

{-|
A configuration languages K₂
is at least as expressive as
another configuration language K₁
iff
we can translate from K₁ to K₂ without losing information.
-}
_≤ᵏ_ : ∀ {I O} → (K₁ K₂ : ConfigurationLanguage I O) → Set
K₁ ≤ᵏ K₂ = ∀ (k₁ : CSyntax K₁) → Σ[ k₂ ∈ CSyntax K₂ ] (K₁ , K₂ ⊢ k₁ ≅ᵏ k₂)

_≡ᵏ_ : ∀ {I O} → (K₁ K₂ : ConfigurationLanguage I O) → Set
K₁ ≡ᵏ K₂ = K₁ ≤ᵏ K₂ × K₂ ≤ᵏ K₁

expressiveness-by-translation : ∀ {I O} {K₁ K₂ : ConfigurationLanguage I O}
  → (t : CSyntax K₁ ⇒ᵏ CSyntax K₂)
  → SemanticsPreserving K₁ K₂ t
  → K₁ ≤ᵏ K₂
expressiveness-by-translation t t-pres = λ k₁ → t k₁ , t-pres k₁

-- B is at least as expressive as A
-- record _≤ᵏ_ (A B : 𝕂) : Set where
--   field
--     to   : A → B
--     from : B → A
--     -- The preservation theorem states that
--     -- all selections made in a configuration A
--     -- are also made in the translated configuration B = to A.
--     -- We need this because
--     -- translating an expression can only preserve semantics
--     -- when translating the respective configurations retains
--     -- all necessary information to configure the translated
--     -- expression.
--     preserves : from ∘ to ≗ id -- this means that the to function is lossless.
-- open _≤ᵏ_ public

-- module Properties
--   {A B : 𝕂}
--   (_≈₁_ : Rel A 0ℓ) -- Equality over the domain
--   (_≈₂_ : Rel B 0ℓ) -- Equality over the codomain
--   where

--   IsExtraction : A ⇒ᵏ B → Set
--   IsExtraction t = ¬ (Injective _≈₁_ _≈₂_ t)

--   Stable : A ⇔ᵏ B → Set
--   Stable cc = from cc ∘ to cc ≗ id -- Maybe this syntactic equality is too strong. We might only need semantically equal configs.
-- open Properties public

-- Lossless : ∀ {A B} → A ⇒ᵏ B → Set

-- _≥ᵏ_ : 𝕂 → 𝕂 → Set
-- A ≥ᵏ B = Σ[ t ∈ A ⇔ᵏ B ] (to t ∘ from t) ≗ id

-- _≡ᵏ_ : 𝕂 → 𝕂 → Set
-- A ≡ᵏ B = Σ[ t ∈ A ⇔ᵏ B ] ((to t ∘ from t) ≗ id × (from t ∘ to t) ≗ id)



{-|
A translated configuration is extensionally equal.
Fixme: Give me a proper name not this ugly one.
-}
-- ExtensionallyEqual-Translation : ∀ {F S Sel} → ConfigEvaluator F S Sel → ConfigTranslation S S → Set
-- ExtensionallyEqual-Translation evalConfig f = ∀ c → evalConfig (f c) ≗ evalConfig c

-- ExtensionallyEqual : ∀ {F S Sel} → ConfigEvaluator F S Sel → ConfigCompiler S S → Set
-- ExtensionallyEqual {F} {S} evalConfig record { to = to ; from = from } =
--   ExtensionallyEqual-Translation {F} {S} evalConfig to × ExtensionallyEqual-Translation {F} {S} evalConfig from

-- -- We identify a configuration to be the same if it can be uniquely translated back
-- -- (i.e., if `to` is an embedding into the second configuration language via its inverse `from`).
-- -- We do not require the inverse direction `from`, being an embedding of configurations from `C₂` into `C₁`, because `C₂` could be larger than `C₁` (when interpreted as a set).
-- -- For example, the set of features in `C₂` could be bigger (e.g., when going from core choice calculus to binary choice calculus) but all information can be derived by `conf` from our initial configuration `c₁`.
-- Stable : ∀ {S₁ S₂} → ConfigCompiler S₁ S₂ → Set
-- Stable cc = from cc ∘ to cc ≗ id -- Maybe this syntactic equality is too strong. We might only need semantically equal configs.

-- _≥ᶜ_ : 𝕂 → 𝕂 → Set
-- C₁ ≥ᶜ C₂ = Σ[ t ∈ C₁ → C₂ ] ?
