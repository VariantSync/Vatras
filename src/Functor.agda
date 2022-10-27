import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Function using (_∘_)
open import Extensionality

record Functor (F : Set → Set) : Set₁ where
  field
    map : ∀ {A B : Set}
      → (A → B)
        ---------
      → F A → F B

    identity : ∀ {A : Set}
        -----------------------
      → map (id {A}) ≡ id {F A}

    composition : ∀ {A B C : Set} → {f : B → C} → {g : A → B}
        ------------------------------
      → map (f ∘ g) ≡ (map f) ∘ (map g)

-- List Functor --
open import Agda.Builtin.List

map_list : ∀ {A B : Set} → (A → B) → List A → List B
map_list f [] = []
map_list f (x ∷ xs) = (f x) ∷ (map_list f xs)

-- map_l_comp : ∀ {A B C : Set} → (f : B → C) → (g : A → B)
--     ------------------------------
--   → map_l (f ∘ g) ≡ (map_l f) ∘ (map_l g)
-- map_l_comp f g =
--   begin
--     map_l (f ∘ g)
--   ≡⟨⟩
-- --    λ {a → (map_l (f ∘ g)) a}
--   ≡⟨⟩
--     ?
--   ≡⟨⟩
--     (map_l f) ∘ (map_l g)
--   ∎

-- functor_l : Functor List
-- functor_l = record
--   { map = map_l
--   ; identity = ?
--   ; composition = map_l_comp
--   }

