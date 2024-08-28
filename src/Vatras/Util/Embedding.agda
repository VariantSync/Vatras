module Vatras.Util.Embedding where

open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≗_)

_embeds-via_ : ∀ {A B : Set}
  → (to   : A → B)
  → (from : B → A)
    --------------
  → Set
to embeds-via from = from ∘ to ≗ id
