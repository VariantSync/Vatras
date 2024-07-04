{-|
This module contains some helper types
for dealing with functions on the syntax
of variability languages.
-}
module Framework.Relation.Function where

open import Framework.Definitions
open import Relation.Binary.PropositionalEquality as Eq using (_≗_; _≡_)
open import Function using (id; _∘_; Injective)

{-|
A pair of functions in both directions.
-}
record _⇔_ (L M : Set) : Set where
  field
    to   : L → M
    from : M → L
open _⇔_ public

{-|
A function that translates expressions of a variability language.
-}
_⇒ₚ_ : 𝔼 → 𝔼 → Set₁
L ⇒ₚ M = ∀ {A} → L A → M A

{-|
A pair of expression translation functions going in both directions.
-}
record _⇔ₚ_ (L M : 𝔼) : Set₁ where
  field
    to   : L ⇒ₚ M
    from : M ⇒ₚ L
open _⇔ₚ_ public

{-|
A translation t from a language L to another language M
constitutes an embedding if there exists an inverse translation t⁻¹.
This means that all expressions in L have a unique counterpart in
M (i.e., the translation is injective).
-}
to-is-Embedding : ∀ {L M : Set} → L ⇔ M → Set
to-is-Embedding t = from t ∘ to t ≗ id

{-|
A translation that is an embedding is always injective.
-}
Embedding→Injective : ∀ {L M : Set}
  → (t : L ⇔ M)
  → to-is-Embedding t
    ------------------------
  → Injective _≡_ _≡_ (to t)
Embedding→Injective t emb {x} {y} to-x≡to-y
  -- By congruence, we can wrap both sides of the equation in from.
  with Eq.cong (from t) to-x≡to-y
... | from-to-x≡from-to-y
    -- By embedding, we can cancel the from ∘ to terms on both sides.
    rewrite emb x | emb y
      = from-to-x≡from-to-y
