import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (_∘_; id)
open import Extensionality

record Functor (F : Set → Set) : Set₁ where
  field
    map : ∀ {A B : Set}
      → (A → B)
        ---------
      → F A → F B

    identity : ∀ {A : Set} {x : F A}
        -----------------------
      → map id x ≡ id x

    composition : ∀ {A B C : Set} → {f : B → C} → {g : A → B}
        ------------------------------
      → map (f ∘ g) ≡ ((map f) ∘ (map g))

-- List Functor --
open import Data.List.Base

list_map_comp : ∀ {A B C : Set} → {f : B → C} → {g : A → B} → {x : List A}
    ------------------------------
  → map (f ∘ g) x ≡ (map f ∘ map g) x
list_map_comp {a} {b} {c} {f} {g} {[]} = refl
list_map_comp {a} {b} {c} {f} {g} {x ∷ xs} =
  begin
    map (f ∘ g) (x ∷ xs)
  ≡⟨⟩
    ((f ∘ g) x) ∷ (map (f ∘ g) xs)
  ≡⟨ cong (_∷_ ((f ∘ g) x)) (list_map_comp {a} {b} {c} {f} {g} {xs}) ⟩
    ((f ∘ g) x) ∷ ((map f ∘ map g) xs)
  ≡⟨⟩
    (f (g x)) ∷ (map f (map g xs))
  ≡⟨⟩
    map f ((g x) ∷ (map g xs))
  ≡⟨⟩
    map f (map g (x ∷ xs))
  ≡⟨⟩
    ((map f) ∘ (map g)) (x ∷ xs)
  ∎

-- functor_l : Functor List
-- functor_l = record
--   { map = map_l
--   ; identity = ?
--   ; composition = map_l_comp
--   }

