module Framework.Relation.Function where

open import Framework.Definitions
open import Relation.Binary.PropositionalEquality as Eq using (_≗_; _≡_)
open import Function using (id; _∘_; Injective)

record _⇔_ (L M : Set) : Set where
  field
    to   : L → M
    from : M → L
open _⇔_ public

_⇒ₚ_ : 𝔼 → 𝔼 → Set₁
L ⇒ₚ M = ∀ {A} → L A → M A

record _⇔ₚ_ (L M : 𝔼) : Set₁ where
  field
    to   : L ⇒ₚ M
    from : M ⇒ₚ L
open _⇔ₚ_ public

{-|
A translation t from a language L₁ to another language L₂
constitutes an embedding if there exists an inverse translation t⁻¹.
This means that all expressions in L₁ have a unique counterpart in
L₂ (i.e., the translation is injective).
-}
to-is-Embedding : ∀ {L M : Set} → L ⇔ M → Set
to-is-Embedding t = from t ∘ to t ≗ id

Embedding→Injective : ∀ {L M : Set}
  → (t : L ⇔ M)
  → to-is-Embedding t
  → Injective _≡_ _≡_ (to t)
Embedding→Injective t emb {x} {y} to-x≡to-y
  -- By congruence, we can wrap both sides of the equation in from.
  with Eq.cong (from t) to-x≡to-y
... | from-to-x≡from-to-y
    -- By embedding, we can cancel the from ∘ to terms on both sides.
    rewrite emb x | emb y
      = from-to-x≡from-to-y
