{-|
Utilities for lists.
-}
module Vatras.Util.List where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.List as List using (List; []; _∷_; lookup; foldr; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _⁺++⁺_) renaming (map to map⁺)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Function using (id; _∘_)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _∸_; _*_; _⊔_; _≤_; _≥_; _<_; s≤s; z≤n)
open import Data.Nat.Properties as ℕ using (m≤m+n)
open import Data.List as List using (List; []; _∷_; lookup; foldr; _++_)
open import Data.List.Properties as List using (map-id; length-++)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; toList; _⁺++⁺_) renaming (map to map⁺)
import Data.List.NonEmpty.Properties as List⁺
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Function using (id; _∘_; flip; const)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; _≢_; refl)

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
last-∷ : ∀ {ℓ} {A : Set ℓ} → (x y : A) → (zs : List A) → List⁺.last (x ∷ y ∷ zs) ≡ List⁺.last (y ∷ zs)
last-∷ x y zs with List.initLast zs
last-∷ x y .[] | [] = refl
last-∷ x y .(xs List.∷ʳ x₁) | xs List.∷ʳ′ x₁ = refl

∈xs++v∷ys⇒∈xs++ys : ∀ {ℓ} {A : Set ℓ}
  → (u v : A)
  → (xs ys : List A)
  → u ≢ v
  → u ∈ (xs List.++ List.[ v ] List.++ ys)
  → u ∈ (xs List.++ ys)
∈xs++v∷ys⇒∈xs++ys u v [] ys u≢v (here u≡v) = ⊥-elim (u≢v u≡v)
∈xs++v∷ys⇒∈xs++ys u v [] ys u≢v (there u∈ys) = u∈ys
∈xs++v∷ys⇒∈xs++ys u v (x ∷ xs) ys u≢v (here u≡x) = here u≡x
∈xs++v∷ys⇒∈xs++ys u v (x ∷ xs) ys u≢v (there u∈xs++v∷ys) = there (∈xs++v∷ys⇒∈xs++ys u v xs ys u≢v u∈xs++v∷ys)

∈∧∉⇒≢ : ∀ {ℓ} {A : Set ℓ} {y z : A}
  → (xs : List A)
  → y ∈ xs
  → All (z ≢_) xs
  → y ≢ z
∈∧∉⇒≢ (x ∷ xs) (here y≡x) (y≢x ∷ z∉xs) y≡z = y≢x (Eq.trans (Eq.sym y≡z) y≡x)
∈∧∉⇒≢ (x ∷ xs) (there y∈xs) (y≢x ∷ z∉xs) y≡z = ∈∧∉⇒≢ xs y∈xs z∉xs y≡z

module _ where
  open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique; _∷_)

  length≤ : ∀ {ℓ} {A : Set ℓ}
    → (xs ys : List A)
    → Unique xs
    → xs ⊆ ys
    → List.length xs ≤ List.length ys
  length≤ [] ys unique-xs xs⊆ys = z≤n
  length≤ (x ∷ xs) ys unique-xs xs⊆ys with List.∈-∃++ (xs⊆ys (here refl))
  length≤ (x ∷ xs) ys (x∉xs ∷ unique-xs) xs⊆ys | l , r , ys≡l++x∷r =
    begin
      List.length (x ∷ xs)
    ≡⟨⟩
      suc (List.length xs)
    ≤⟨ s≤s (length≤ xs (l List.++ r) unique-xs λ {y} y∈xs → ∈xs++v∷ys⇒∈xs++ys y x l r (∈∧∉⇒≢ xs y∈xs x∉xs) (Eq.subst (y ∈_) ys≡l++x∷r (xs⊆ys (there y∈xs)))) ⟩
      suc (List.length (l List.++ r))
    ≡⟨ Eq.cong suc (length-++ l) ⟩
      suc (List.length l + List.length r)
    ≡⟨ ℕ.+-suc (List.length l) (List.length r) ⟨
      List.length l + suc (List.length r)
    ≡⟨⟩
      List.length l + List.length (x ∷ r)
    ≡⟨ length-++ l ⟨
      List.length (l List.++ (x ∷ r))
    ≡⟨ Eq.cong List.length ys≡l++x∷r ⟨
      List.length ys
    ∎
    where
    open ℕ.≤-Reasoning

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

find-or-last-last : ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ) (xs : List⁺ A)
  → suc n ≥ List⁺.length xs
  → find-or-last n xs ≡ List⁺.last xs
find-or-last-last n (x ∷ []) n≥xs = refl
find-or-last-last (suc n) (x ∷ y ∷ zs) (s≤s n≥xs) = Eq.trans (find-or-last-last n (y ∷ zs) n≥xs) (Eq.sym (last-∷ x y zs))

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

sum-map-≤-with∈ : ∀ {ℓ} {A : Set ℓ}
  → {f g : A → ℕ}
  → (xs : List A)
  → (∀ (x : A) → x ∈ xs → f x ≤ g x)
  → List.sum (List.map f xs) ≤ List.sum (List.map g xs)
sum-map-≤-with∈ {f = f} {g = g} [] f≤g = ℕ.≤-refl
sum-map-≤-with∈ {f = f} {g = g} (x ∷ xs) f≤g =
  begin
    List.sum (List.map f (x ∷ xs))
  ≡⟨⟩
    f x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoˡ-≤ (List.sum (List.map f xs)) (f≤g x (here refl)) ⟩
    g x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoʳ-≤ (g x) (sum-map-≤-with∈ xs (λ y y∈ys → f≤g y (there y∈ys))) ⟩
    g x + List.sum (List.map g xs)
  ≡⟨⟩
    List.sum (List.map g (x ∷ xs))
  ∎
  where
  open ℕ.≤-Reasoning

sum-map-≤ : ∀ {ℓ} {A : Set ℓ}
  → (f g : A → ℕ)
  → (xs : List A)
  → (∀ x → f x ≤ g x)
  → List.sum (List.map f xs) ≤ List.sum (List.map g xs)
sum-map-≤ f g xs f≤g = sum-map-≤-with∈ xs λ x x∈xs → f≤g x

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

sum-map-const :
  ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ)
  → (xs : List A)
  → List.sum (List.map (const n) xs) ≡ n * List.length xs
sum-map-const n [] = Eq.sym (ℕ.*-zeroʳ n)
sum-map-const n (x ∷ xs) =
    List.sum (List.map (const n) (x ∷ xs))
  ≡⟨⟩
    n + List.sum (List.map (const n) xs)
  ≡⟨ Eq.cong (n +_) (sum-map-const n xs) ⟩
    n + n * List.length xs
  ≡⟨ ℕ.*-suc n (List.length xs) ⟨
    n * suc (List.length xs)
  ≡⟨⟩
    n * List.length (x ∷ xs)
  ∎
  where
  open Eq.≡-Reasoning

sum-+ : ∀ (n : ℕ) (xs : List ℕ) → List.sum (List.map (n +_) xs) ≡ n * List.length xs + List.sum xs
sum-+ n [] = Eq.trans (Eq.sym (ℕ.*-zeroʳ n)) (Eq.sym (ℕ.+-identityʳ (n * 0)))
sum-+ n (x ∷ xs) =
  begin
    List.sum (List.map (n +_) (x ∷ xs))
  ≡⟨⟩
    n + x + List.sum (List.map (n +_) xs)
  ≡⟨ Eq.cong (n + x +_) (sum-+ n xs) ⟩
    n + x + (n * List.length xs + List.sum xs)
  ≡⟨ Eq.cong (_+ (n * List.length xs + List.sum xs)) (ℕ.+-comm n x) ⟩
    x + n + (n * List.length xs + List.sum xs)
  ≡⟨ ℕ.+-assoc (x + n) (n * List.length xs) (List.sum xs) ⟨
    (x + n + n * List.length xs) + List.sum xs
  ≡⟨ Eq.cong (_+ List.sum xs) (ℕ.+-assoc x n (n * List.length xs)) ⟩
    (x + (n + n * List.length xs)) + List.sum xs
  ≡⟨ Eq.cong (_+ List.sum xs) (ℕ.+-comm x (n + n * List.length xs)) ⟩
    ((n + n * List.length xs) + x) + List.sum xs
  ≡⟨ ℕ.+-assoc (n + n * List.length xs) x (List.sum xs) ⟩
    (n + n * List.length xs) + (x + List.sum xs)
  ≡⟨ Eq.cong (_+ (x + List.sum xs)) (ℕ.*-suc n (List.length xs)) ⟨
    n * suc (List.length xs) + (x + List.sum xs)
  ≡⟨⟩
    n * List.length (x ∷ xs) + List.sum (x ∷ xs)
  ∎
  where
  open Eq.≡-Reasoning

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

module _ where
  open import Data.List.Relation.Binary.Sublist.Propositional using (_⊇_; []; _∷_; _∷ʳ_)
  import Data.List.Relation.Binary.Sublist.Propositional.Properties as Sublist
  open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
  open import Relation.Binary using (Rel; _Respects_)

  AllPairs-resp-⊆ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → {R : Rel A ℓ₂} → (AllPairs R) Respects _⊇_
  AllPairs-resp-⊆ [] [] = []
  AllPairs-resp-⊆ (y ∷ʳ xs⊇ys) (All-x ∷ AllPairs-xs) = AllPairs-resp-⊆ xs⊇ys AllPairs-xs
  AllPairs-resp-⊆ {x = .(_ ∷ _)} {.(_ ∷ _)} (refl ∷ xs⊇ys) (All-x ∷ AllPairs-xs) = Sublist.All-resp-⊆ xs⊇ys All-x ∷ AllPairs-resp-⊆ xs⊇ys AllPairs-xs

  AllPairs-++⁻ˡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → A → Set ℓ₂}
    → (xs : List A) {ys : List A}
    → AllPairs P (xs ++ ys)
    → AllPairs P xs
  AllPairs-++⁻ˡ [] allPairs = []
  AllPairs-++⁻ˡ (x ∷ xs) (P-x ∷ allPairs) = All.++⁻ˡ xs P-x ∷ AllPairs-++⁻ˡ xs allPairs

  AllPairs-++⁻ʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → A → Set ℓ₂}
    → (xs : List A) {ys : List A}
    → AllPairs P (xs ++ ys)
    → AllPairs P ys
  AllPairs-++⁻ʳ [] allPairs = allPairs
  AllPairs-++⁻ʳ (x ∷ xs) allPairs = AllPairs-++⁻ʳ xs (AllPairs.tail allPairs)

  AllPairs⇒AllAll : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → A → Set ℓ₂}
    → (xs ys : List A)
    → AllPairs P (xs ++ ys)
    → All (λ y → All (P y) ys) xs
  AllPairs⇒AllAll [] ys allPairs = []
  AllPairs⇒AllAll (x ∷ xs) ys (P-x ∷ allPairs) = All.++⁻ʳ xs P-x ∷ AllPairs⇒AllAll xs ys allPairs

  AllAll-comm : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → A → Set ℓ₂}
    → (xs ys : List A)
    → (∀ {x} {y} → P x y → P y x)
    → All (λ y → All (P y) xs) ys
    → All (λ y → All (P y) ys) xs
  AllAll-comm [] ys sym all-all = []
  AllAll-comm (x ∷ xs) ys sym all-all = All.map (λ All-P-y-xs → sym (All.head All-P-y-xs)) all-all ∷ AllAll-comm xs ys sym (All.map All.tail all-all)

module _ where
  open import Data.List.Relation.Ternary.Interleaving.Propositional using (Interleaving; []; consˡ; consʳ)
  open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)

  Interleaving⇒Sublistˡ : ∀ {ℓ} {A : Set ℓ}
    → {xs ys zs : List A}
    → Interleaving xs ys zs
    → xs ⊆ zs
  Interleaving⇒Sublistˡ [] = []
  Interleaving⇒Sublistˡ (consˡ zs) = refl ∷ Interleaving⇒Sublistˡ zs
  Interleaving⇒Sublistˡ (consʳ zs) = _ ∷ʳ Interleaving⇒Sublistˡ zs

  Interleaving⇒Sublistʳ : ∀ {ℓ} {A : Set ℓ}
    → {xs ys zs : List A}
    → Interleaving xs ys zs
    → ys ⊆ zs
  Interleaving⇒Sublistʳ [] = []
  Interleaving⇒Sublistʳ (consˡ zs) = _ ∷ʳ Interleaving⇒Sublistʳ zs
  Interleaving⇒Sublistʳ (consʳ zs) = refl ∷ Interleaving⇒Sublistʳ zs

  All-Interleavingₗ :
    ∀ {a} {p} {A : Set a} {P : A → Set p}
    → {xs ys zs : List A}
    → Interleaving xs ys zs
    → All P zs
    → All P xs
  All-Interleavingₗ [] [] = []
  All-Interleavingₗ (consˡ interleaving) (pz ∷ all-zs) = pz ∷ All-Interleavingₗ interleaving all-zs
  All-Interleavingₗ (consʳ interleaving) (pz ∷ all-zs) = All-Interleavingₗ interleaving all-zs

  All-Interleavingᵣ :
    ∀ {a} {p} {A : Set a} {P : A → Set p}
    → {xs ys zs : List A}
    → Interleaving xs ys zs
    → All P zs
    → All P ys
  All-Interleavingᵣ [] [] = []
  All-Interleavingᵣ (consˡ interleaving) (pz ∷ all-zs) = All-Interleavingᵣ interleaving all-zs
  All-Interleavingᵣ (consʳ interleaving) (pz ∷ all-zs) = pz ∷ All-Interleavingᵣ interleaving all-zs

  map-Interleaving :
    ∀ {a} {b} {A : Set a} {B : Set b}
    → {f : A → B}
    → {xs ys zs : List A}
    → Interleaving xs ys zs
    → Interleaving (List.map f xs) (List.map f ys) (List.map f zs)
  map-Interleaving [] = []
  map-Interleaving (consˡ interleaving) = consˡ (map-Interleaving interleaving)
  map-Interleaving (consʳ interleaving) = consʳ (map-Interleaving interleaving)

  sum-Interleaving :
    ∀ {xs ys zs : List ℕ}
    → Interleaving xs ys zs
    → List.sum xs + List.sum ys ≡ List.sum zs
  sum-Interleaving [] = refl
  sum-Interleaving {x ∷ xs} {ys} {.x ∷ zs} (consˡ interleaving) =
      List.sum (x ∷ xs) + List.sum ys
    ≡⟨⟩
      x + List.sum xs + List.sum ys
    ≡⟨ ℕ.+-assoc x (List.sum xs) (List.sum ys) ⟩
      x + (List.sum xs + List.sum ys)
    ≡⟨ Eq.cong (x +_) (sum-Interleaving interleaving) ⟩
      x + List.sum zs
    ≡⟨⟩
      List.sum (x ∷ zs)
    ∎
    where
    open Eq.≡-Reasoning
  sum-Interleaving {xs} {y ∷ ys} {.y ∷ zs} (consʳ interleaving) =
      List.sum xs + List.sum (y ∷ ys)
    ≡⟨⟩
      List.sum xs + (y + List.sum ys)
    ≡⟨ ℕ.+-assoc (List.sum xs) y (List.sum ys) ⟨
      List.sum xs + y + List.sum ys
    ≡⟨ Eq.cong (_+ List.sum ys) (ℕ.+-comm (List.sum xs) y) ⟩
      y + List.sum xs + List.sum ys
    ≡⟨ ℕ.+-assoc y (List.sum xs) (List.sum ys) ⟩
      y + (List.sum xs + List.sum ys)
    ≡⟨ Eq.cong (y +_) (sum-Interleaving interleaving) ⟩
      y + List.sum zs
    ≡⟨⟩
      List.sum (y ∷ zs)
    ∎
    where
    open Eq.≡-Reasoning

applyUpTo-cong : ∀ {ℓ₁} {A : Set ℓ₁}
  → {f g : ℕ → A}
  → f ≗ g
  → List.applyUpTo f ≗ List.applyUpTo g
applyUpTo-cong f≗g zero = refl
applyUpTo-cong f≗g (suc n) = Eq.cong₂ _∷_ (f≗g zero) (applyUpTo-cong (f≗g ∘ suc) n)

applyUpTo-∷ʳ⁺ : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) (n : ℕ) → List.applyUpTo f n List.∷ʳ f n ≡ List.applyUpTo f (suc n)
applyUpTo-∷ʳ⁺ f zero = refl
applyUpTo-∷ʳ⁺ f (suc n) = Eq.cong (f 0 ∷_) (applyUpTo-∷ʳ⁺ (f ∘ suc) n)

applyUpTo-++⁺ : ∀ {ℓ} {A : Set ℓ}
  → (f : ℕ → A)
  → (n m : ℕ)
  → List.applyUpTo f (n + m) ≡ List.applyUpTo f n ++ List.applyUpTo (λ i → f (n + i)) m
applyUpTo-++⁺ f zero m = refl
applyUpTo-++⁺ f (suc n) m = Eq.cong (f zero ∷_) (applyUpTo-++⁺ (f ∘ suc) n m)

upTo-m∸upTo-n>m : ∀ {m n : ℕ} → n ≤ m → m ≤ List.sum (List.upTo (suc m)) ∸ List.sum (List.upTo n)
upTo-m∸upTo-n>m {m} {n} n≤m =
  begin
    m
  ≡⟨ ℕ.m+n∸m≡n n m ⟨
    n + m ∸ n
  ≡⟨ ℕ.+-∸-assoc n n≤m ⟩
    n + (m ∸ n)
  ≡⟨ ℕ.+-identityʳ (n + (m ∸ n)) ⟨
    n + (m ∸ n) + 0
  ≤⟨ ℕ.m≤n+m ((n + (m ∸ n) + 0)) (List.sum (List.applyUpTo (n +_) (m ∸ n))) ⟩
    List.sum (List.applyUpTo (n +_) (m ∸ n)) + (n + (m ∸ n) + 0)
  ≡⟨ List.sum-++ (List.applyUpTo (n +_) (m ∸ n)) (n + (m ∸ n) ∷ []) ⟨
    List.sum (List.applyUpTo (n +_) (m ∸ n) List.∷ʳ (n + (m ∸ n)))
  ≡⟨ Eq.cong List.sum (applyUpTo-∷ʳ⁺ (n +_) (m ∸ n)) ⟩
    List.sum (List.applyUpTo (n +_) (suc (m ∸ n)))
  ≡⟨ Eq.cong (λ x → List.sum (List.applyUpTo (n +_) x)) (ℕ.+-∸-assoc 1 n≤m) ⟨
    List.sum (List.applyUpTo (n +_) (suc m ∸ n))
  ≡⟨ ℕ.m+n∸m≡n (List.sum (List.upTo n)) (List.sum (List.applyUpTo (n +_) (suc m ∸ n))) ⟨
    List.sum (List.upTo n) + List.sum (List.applyUpTo (n +_) (suc m ∸ n)) ∸ List.sum (List.upTo n)
  ≡⟨ Eq.cong (_∸ List.sum (List.upTo n)) (List.sum-++ (List.upTo n) (List.applyUpTo (n +_) (suc m ∸ n))) ⟨
    List.sum (List.upTo n ++ List.applyUpTo (n +_) (suc m ∸ n)) ∸ List.sum (List.upTo n)
  ≡⟨ Eq.cong (λ x → List.sum x ∸ List.sum (List.upTo n)) (applyUpTo-++⁺ id n (suc m ∸ n)) ⟨
    List.sum (List.upTo (n + (suc m ∸ n))) ∸ List.sum (List.upTo n)
  ≡⟨ Eq.cong (λ x → List.sum (List.upTo x) ∸ List.sum (List.upTo n)) (ℕ.+-∸-assoc n (ℕ.≤-trans n≤m (ℕ.n≤1+n m))) ⟨
    List.sum (List.upTo (n + suc m ∸ n)) ∸ List.sum (List.upTo n)
  ≡⟨ Eq.cong (λ x → List.sum (List.upTo x) ∸ List.sum (List.upTo n)) (ℕ.m+n∸m≡n n (suc m)) ⟩
    List.sum (List.upTo (suc m)) ∸ List.sum (List.upTo n)
  ∎
  where
  open ℕ.≤-Reasoning
