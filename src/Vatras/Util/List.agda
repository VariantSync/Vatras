{-|
Utilities for lists.
-}
module Vatras.Util.List where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _∸_; _*_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties as ℕ using (m≤m+n)
open import Data.List as List using (List; []; _∷_; lookup; foldr; _++_)
open import Data.List.Properties using (map-id; length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; toList; _⁺++⁺_) renaming (map to map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Function using (id; _∘_; flip; const)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

-- true iff the given list is empty
empty? : ∀ {A : Set} → List A → Bool
empty? [] = true
empty? (_ ∷ _) = false

max : List ℕ → ℕ
max = foldr _⊔_ zero

max-≤ : (n : ℕ) → (xs : List ℕ) → n ∈ xs → n ≤ max xs
max-≤ n [] ()
max-≤ n (.n ∷ xs) (here refl) = ℕ.m≤m⊔n n (max xs)
max-≤ n (x ∷ xs) (there x∈xs) = ℕ.≤-trans (max-≤ n xs x∈xs) (ℕ.m≤n⊔m x (max xs))

-- TODO: Contribute to stl
⁺++⁺-length : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A)
  → List⁺.length (xs ⁺++⁺ ys) ≡ List⁺.length xs + List⁺.length ys
⁺++⁺-length (x ∷ xs) (y ∷ ys) = length-++ (x ∷ xs)

⁺++⁺-length-≤ : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A) → List⁺.length xs ≤ List⁺.length (xs ⁺++⁺ ys)
⁺++⁺-length-≤ xs ys rewrite ⁺++⁺-length xs ys = m≤m+n (List⁺.length xs) (List⁺.length ys)

++-tail : ∀ {ℓ} {A : Set ℓ} (y : A) (ys xs : List A)
  → (xs ++ y ∷ []) ++ ys ≡ xs ++ y ∷ ys
++-tail y ys [] = refl
++-tail y ys (x ∷ xs) = Eq.cong (x ∷_) (++-tail y ys xs)

-- Do not touch this function. its definition is very fragile and just refactoring it can break proofs.
find-or-last : ∀ {ℓ} {A : Set ℓ} → ℕ → List⁺ A → A
find-or-last _ (x ∷ []) = x
find-or-last zero (x ∷ y ∷ zs) = x
find-or-last (suc i) (x ∷ y ∷ zs) = find-or-last i (y ∷ zs)
-- find-or-last (x ∷ []) _ = x
-- find-or-last (x ∷ y ∷ zs) zero = x
-- find-or-last (x ∷ y ∷ zs) (suc i) = find-or-last (y ∷ zs) i

find-or-last-zero : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : List A)
  → find-or-last zero (x ∷ xs) ≡ x
find-or-last-zero _ [] = refl
find-or-last-zero _ (_ ∷ _) = refl

map-find-or-last : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → (i : ℕ)
  → f ∘ (find-or-last i) ≗ (find-or-last i) ∘ (map⁺ f)
map-find-or-last f zero (head ∷ []) = refl
map-find-or-last f zero (head ∷ x ∷ tail) = refl
map-find-or-last f (suc i) (x ∷ []) = refl
map-find-or-last f (suc i) (x ∷ y ∷ zs) =
  begin
    (f ∘ find-or-last (suc i)) (x ∷ y ∷ zs)
  ≡⟨⟩
    (f ∘ find-or-last i) (y ∷ zs)
  ≡⟨ map-find-or-last f i (y ∷ zs) ⟩
    (find-or-last i ∘ map⁺ f) (y ∷ zs)
  ≡⟨⟩
    (find-or-last (suc i) ∘ map⁺ f) (x ∷ y ∷ zs)
  ∎
  where
  open Eq.≡-Reasoning

find-or-last⇒lookup : ∀ {ℓ} {A : Set ℓ} {i : ℕ}
  → (x : A)
  → (xs : List A)
  → find-or-last i (x ∷ xs) ≡ Vec.lookup (x ∷ Vec.fromList xs) (ℕ≥.cappedFin i)
find-or-last⇒lookup {i = i} x [] = refl
find-or-last⇒lookup {i = zero} x (y ∷ ys) = refl
find-or-last⇒lookup {i = suc i} x (y ∷ ys) = find-or-last⇒lookup y ys

lookup⇒find-or-last : ∀ {ℓ} {A : Set ℓ} {n m : ℕ}
  → (vec : Vec A (suc n))
  → Vec.lookup vec (ℕ≥.cappedFin m) ≡ find-or-last m (List⁺.fromVec vec)
lookup⇒find-or-last {n = zero} {m = m} (x ∷ []) = refl
lookup⇒find-or-last {n = suc n} {m = zero} (x ∷ y ∷ ys) = refl
lookup⇒find-or-last {n = suc n} {m = suc m} (x ∷ y ∷ ys) = lookup⇒find-or-last (y ∷ ys)

find-or-last-append : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → n < List⁺.length xs
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last n xs
find-or-last-append {n = .zero} (x ∷ [])     (y ∷ ys) (s≤s z≤n) = refl
find-or-last-append {n =  zero} (x ∷ z ∷ zs) (y ∷ ys) (s≤s le)  = refl
find-or-last-append {n = suc n} (x ∷ z ∷ zs) (y ∷ ys) (s≤s (n≤zzs)) = find-or-last-append (z ∷ zs) (y ∷ ys) (n≤zzs)

find-or-last-prepend-+ : ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ)
  → (xs ys : List⁺ A)
  → find-or-last (List⁺.length xs + n) (xs ⁺++⁺ ys) ≡ find-or-last n ys
find-or-last-prepend-+ n (x ∷ xs) ys = ind n x xs ys
  where
    -- We need this indirection for termination checking.
    -- We have to unpack the first list into two parameters.
    ind : ∀ {ℓ} {A : Set ℓ}
      → (n : ℕ)
      → (x : A)
      → (xs : List A)
      → (ys : List⁺ A)
      → find-or-last (List⁺.length (x ∷ xs) + n) ((x ∷ xs) ⁺++⁺ ys) ≡ find-or-last n ys
    ind n x [] ys = refl
    ind n x (z ∷ zs) ys = ind n z zs ys

find-or-last-prepend-∸ : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → List⁺.length xs ≤ n
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last (n ∸ List⁺.length xs) ys
find-or-last-prepend-∸ {n = zero} xs ys ()
find-or-last-prepend-∸ {n = suc n} (x ∷ []) ys (s≤s z≤n) = refl
find-or-last-prepend-∸ {n = suc n} (x ∷ z ∷ zs) ys (s≤s smol) =
  begin
    find-or-last (suc n) ((x ∷ z ∷ zs) ⁺++⁺ ys)
  ≡⟨⟩
    find-or-last n ((z ∷ zs) ⁺++⁺ ys)
  ≡⟨ find-or-last-prepend-∸ (z ∷ zs) ys smol ⟩
    find-or-last (n ∸ List⁺.length (z ∷ zs)) ys
  ≡⟨⟩
    find-or-last (suc n ∸ suc (List⁺.length (z ∷ zs))) ys
  ≡⟨⟩
    find-or-last (suc n ∸ List⁺.length (x ∷ z ∷ zs)) ys
  ∎
  where
  open Eq.≡-Reasoning

-- Todo: Contribute this to Agda stdlib
map⁺-id : ∀ {ℓ} {A : Set ℓ} → map⁺ id ≗ id {A = List⁺ A}
map⁺-id (head ∷ tail) = Eq.cong (head ∷_) (map-id tail)

map-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → (b : B)
  → (xs : List A)
  → List.map (const b) xs ≡ List.replicate (List.length xs) b
map-const b [] = refl
map-const b (x ∷ xs) = Eq.cong (b ∷_) (map-const b xs)

map-cong-with∈ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → {f g : A → B}
  → (xs : List A)
  → (∀ (x : A) → x ∈ xs → f x ≡ g x)
  → List.map f xs ≡ List.map g xs
map-cong-with∈ [] f≗g = refl
map-cong-with∈ (x ∷ xs) f≗g = Eq.cong₂ _∷_ (f≗g x (here refl)) (map-cong-with∈ xs (λ x x∈xs → f≗g x (there x∈xs)))

sum-replicate : (n m : ℕ) → List.sum (List.replicate n m) ≡ n * m
sum-replicate zero m = refl
sum-replicate (suc n) m = Eq.cong (m +_) (sum-replicate n m)

sum-map-≤ : ∀ {ℓ} {A : Set ℓ}
  → (f g : A → ℕ)
  → (xs : List A)
  → (∀ x → f x ≤ g x)
  → List.sum (List.map f xs) ≤ List.sum (List.map g xs)
sum-map-≤ f g [] f≤g = z≤n
sum-map-≤ f g (x ∷ xs) f≤g =
  begin
    List.sum (List.map f (x ∷ xs))
  ≡⟨⟩
    f x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoˡ-≤ (List.sum (List.map f xs)) (f≤g x) ⟩
    g x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoʳ-≤ (g x) (sum-map-≤ f g xs f≤g) ⟩
    g x + List.sum (List.map g xs)
  ≡⟨⟩
    List.sum (List.map g (x ∷ xs))
  ∎
  where
  open ℕ.≤-Reasoning

sum-map-< :
  ∀ {ℓ} {A : Set ℓ}
  → (f g : A → ℕ)
  → (xs : List A)
  → (∀ x → f x < g x)
  → List.sum (List.map f xs) ≤ List.sum (List.map g xs) ∸ List.length xs
sum-map-< f g [] f<g = z≤n
sum-map-< f g (x ∷ xs) f<g =
  begin
    List.sum (List.map f (x ∷ xs))
  ≡⟨⟩
    f x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoˡ-≤ (List.sum (List.map f xs)) (ℕ.<⇒≤pred (f<g x)) ⟩
    (g x ∸ 1) + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoʳ-≤ (g x ∸ 1) (sum-map-< f g xs f<g) ⟩
    (g x ∸ 1) + (List.sum (List.map g xs) ∸ List.length xs)
  ≡⟨ ℕ.+-∸-assoc (g x ∸ 1) (
    begin
      List.length xs
    ≡⟨ ℕ.*-identityʳ (List.length xs) ⟨
      List.length xs * 1
    ≡⟨ sum-replicate (List.length xs) 1 ⟨
      List.sum (List.replicate (List.length xs) 1)
    ≡⟨ Eq.cong List.sum (map-const 1 xs) ⟨
      List.sum (List.map (const 1) xs)
    ≤⟨ sum-map-≤ (const 1) g xs (λ x → ℕ.≤-trans (s≤s z≤n) (f<g x)) ⟩
      List.sum (List.map g xs)
    ∎)
  ⟨
    ((g x ∸ 1) + List.sum (List.map g xs)) ∸ List.length xs
  ≡⟨ Eq.cong (_∸ List.length xs) (ℕ.+-∸-comm (List.sum (List.map g xs)) (ℕ.≤-trans (s≤s z≤n) (f<g x))) ⟨
    ((g x + List.sum (List.map g xs)) ∸ 1) ∸ List.length xs
  ≡⟨ ℕ.∸-+-assoc ((g x + List.sum (List.map g xs))) 1 (List.length xs)⟩
    List.sum (List.map g (x ∷ xs)) ∸ List.length (x ∷ xs)
  ∎
  where
  open ℕ.≤-Reasoning

sum-* : ∀ (n : ℕ) (xs : List ℕ) → List.sum (List.map (n *_) xs) ≡ n * List.sum xs
sum-* n [] = Eq.sym (ℕ.*-zeroʳ n)
sum-* n (x ∷ xs) =
  begin
    List.sum (List.map (n *_) (x ∷ xs))
  ≡⟨⟩
    n * x + List.sum (List.map (n *_) xs)
  ≡⟨ Eq.cong (n * x +_) (sum-* n xs) ⟩
    n * x + n * List.sum xs
  ≡⟨ ℕ.*-distribˡ-+ n x (List.sum xs) ⟨
    n * (x + List.sum xs)
  ≡⟨⟩
    n * List.sum (x ∷ xs)
  ∎
  where
  open Eq.≡-Reasoning
