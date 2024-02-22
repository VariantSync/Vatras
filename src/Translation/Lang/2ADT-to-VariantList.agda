open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.2ADT-to-VariantList
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; _++⁺_; _⁺++⁺_; toList; length)
open import Data.List.NonEmpty.Properties using (length-++⁺)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤ᵇ_; z≤n; s≤s; s<s) --_≤?_)
open import Data.Nat.Properties using (≤-trans; <⇒≤; m≤m+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Level using (0ℓ)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)

open import Data.EqIndexedSet hiding (Index; _∈_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (does; proof; yes; no; False; True; fromWitness; toWitness; fromWitnessFalse)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Lang.2ADT F V
  using (2ADT; leaf; _⟨_,_⟩)
  renaming (⟦_⟧ to ⟦_⟧₂; Configuration to Conf₂)
open import Lang.VariantList V
  using (VariantList)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Confₗ)

-- imports for nicer holes
open import Util.List using (find-or-last)
open Data.List using (_++_; foldr)
open Data.List.NonEmpty using (head; tail)

record Selection : Set where
  constructor _↣_
  field
    feature : F
    value : Bool

Path : Set
Path = List Selection

different : Rel Selection 0ℓ
different (A ↣ _) (B ↣ _) = False (A == B)

same : Rel Selection 0ℓ
same (A ↣ _) (B ↣ _) = True (A == B)

is : F → Selection → Set
is A (B ↣ _) = True (A == B)

_∈_ : F → Path → Set
a ∈ as = Any (is a) as

getValue : ∀ {a fs} → a ∈ fs → Bool
getValue (here {_ ↣ value} _) = value
getValue (there fs) = getValue fs

_∈?_ : Decidable _∈_
a ∈? [] = no λ ()
a ∈? ((x ↣ v) ∷ xs) with a == x
... | yes p = yes (here (fromWitness p))
... | no ¬p with a ∈? xs
...   | yes q = yes (there q)
...   | no ¬q = no nope
  where
    nope : ¬ Any (is a) ((x ↣ v) ∷ xs)
    nope (here  p) = ¬p (toWitness p)
    nope (there q) = ¬q q

flip : ∀ {b} → (as : Path) → ¬ b ∈ as → All (different (b ↣ true)) as
flip [] _ = []
flip (a ∷ as) nope =
    fromWitnessFalse (λ x → nope (here (fromWitness x)))
  ∷ flip as λ x → nope (there x)

Unique : Path → Set
Unique = AllPairs different

-- All paths from a leaf to the root choice are unique.
data UniquePaths : ∀ {A} → Path → 2ADT A → Set where
  -- At a leaf, any path of unique feature names might have ended here.
  oleaf : ∀ {A} {v : V A} {above : Path}
    → Unique above
      -----------------------
    → UniquePaths above (leaf v)

  -- Any path 'above' can lead to a choice, when it is legal
  -- to continue it downwards with configuring the choice.
  ochc : ∀ {A} {D : F} {l r : 2ADT A} {above : Path}
    → UniquePaths ((D ↣ true)  ∷ above) l
    → UniquePaths ((D ↣ false) ∷ above) r
      ------------------------------------
    → UniquePaths above (D ⟨ l , r ⟩)

record UniquePaths2ADTBelow (above : Path) (A : 𝔸) : Set where
  constructor _⊚_ -- \oo
  field
    node   : 2ADT A
    unique : UniquePaths above node
open UniquePaths2ADTBelow public

UniquePaths2ADT : 𝔼
UniquePaths2ADT = UniquePaths2ADTBelow []

ordinary-to-unique' : ∀ {A}
  → (above : Path)
  → Unique above
  → 2ADT A
  → UniquePaths2ADTBelow above A
ordinary-to-unique' _ u (leaf v) = leaf v ⊚ oleaf u
ordinary-to-unique' {A} above u (D ⟨ l , r ⟩) with D ∈? above
... | yes D∈above =
  if getValue D∈above
  then ordinary-to-unique' above u l
  else ordinary-to-unique' above u r
... | no  D∉above = (D ⟨ node rec-l , node rec-r ⟩) ⊚ ochc (unique rec-l) (unique rec-r)
  where
    uuu : ∀ (b : Bool) → Unique ((D ↣ b) ∷ above)
    uuu _ = flip above D∉above ∷ u

    rec-l : UniquePaths2ADTBelow ((D ↣ true) ∷ above) A
    rec-l = ordinary-to-unique' ((D ↣ true) ∷ above) (uuu true) l

    rec-r : UniquePaths2ADTBelow ((D ↣ false) ∷ above) A
    rec-r = ordinary-to-unique' ((D ↣ false) ∷ above) (uuu false) r

ordinary-to-unique : ∀ {A} → 2ADT A → UniquePaths2ADT A
ordinary-to-unique e = ordinary-to-unique' [] [] e

unique-to-ordinary : ∀ {A} → UniquePaths2ADT A → 2ADT A
unique-to-ordinary = node

-- FIXME: THIS IS WRONG: We have to make unique first
tr : ∀ {A : 𝔸} → 2ADT A → VariantList A
tr (leaf v)      = v ∷ []
tr (D ⟨ l , r ⟩) = tr l ⁺++⁺ tr r

leaf-count : ∀ {A : 𝔸} → 2ADT A → ℕ
leaf-count (leaf _) = 1
leaf-count (D ⟨ l , r ⟩) = leaf-count l + leaf-count r

open import Data.List.Properties using (length-++)
length-⁺++⁺ : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A)
  → length (xs ⁺++⁺ ys) ≡ length xs + length ys
length-⁺++⁺ (x ∷ xs) (y ∷ ys) = length-++ (x ∷ xs)
  -- begin
  --   length ((x ∷ xs) ⁺++⁺ (y ∷ ys))
  -- ≡⟨⟩
  --   suc (Data.List.length (xs ++ y ∷ ys))
  -- ≡⟨⟩
  --   Data.List.length (x ∷ xs ++ (y ∷ ys))
  -- ≡⟨ length-++ (x ∷ xs) ⟩
  --   Data.List.length (x ∷ xs) + Data.List.length (y ∷ ys)
  -- ≡⟨⟩
  --   length (x ∷ xs) + length (y ∷ ys)
  -- ∎

<-cong : ∀ {m n} (a : ℕ) → m < n → a + m < a + n
<-cong zero x = x
<-cong (suc a) x = s≤s (<-cong a x)

append-preserves : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → n < length xs
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last n xs
append-preserves {n = .zero} (x ∷ [])     (y ∷ ys) (s≤s z≤n) = refl
append-preserves {n =  zero} (x ∷ z ∷ zs) (y ∷ ys) (s≤s le)  = refl
append-preserves {n = suc n} (x ∷ z ∷ zs) (y ∷ ys) (s≤s (n≤zzs)) = append-preserves (z ∷ zs) (y ∷ ys) (n≤zzs)

-- FIXME: Remove this macro
{-# TERMINATING #-}
prepend-preserves : ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ)
  → (xs ys : List⁺ A)
  → find-or-last (length xs + n) (xs ⁺++⁺ ys) ≡ find-or-last n ys
prepend-preserves n (x ∷ []) ys = refl
prepend-preserves zero (x ∷ z ∷ zs) ys = prepend-preserves zero (z ∷ zs) ys
prepend-preserves (suc n) (x ∷ z ∷ zs) ys = prepend-preserves (suc n) (z ∷ zs) ys
-- prepend-preserves n (x ∷ z ∷ zs) (y ∷ ys) =
--   begin
--     find-or-last (length (x ∷ z ∷ zs) + n) ((x ∷ z ∷ zs) ⁺++⁺ (y ∷ ys))
--   ≡⟨⟩
--     find-or-last (length (x ∷ z ∷ zs) + n) (x ∷ ((z ∷ zs) ++ (y ∷ ys)))
--   ≡⟨⟩
--     find-or-last (length (z ∷ zs) + n) (((z ∷ zs) ⁺++⁺ (y ∷ ys)))
--   ≡⟨ prepend-preserves n (z ∷ zs) (y ∷ ys) ⟩
--     find-or-last n (y ∷ ys)
--   ∎

conf : ∀ {A} → 2ADT A → Conf₂ → ℕ
conf (leaf v) c = 0
conf (D ⟨ l , r ⟩) c with c D
... | true  = conf l c
... | false = length (tr l) + conf r c


conf-bounded : ∀ {A}
  → (e : 2ADT A)
  → (c : Conf₂)
  → conf e c < length (tr e)
conf-bounded (leaf v) c = s≤s z≤n
conf-bounded (D ⟨ l , r ⟩) c with c D in eq
... | true = ≤-trans (conf-bounded l c) foo
  where
    foo : length (tr l) ≤ length (tr l ⁺++⁺ tr r)
    foo rewrite length-⁺++⁺ (tr l) (tr r)
      = m≤m+n (length (tr l)) (length (tr r))
... | false = go
  where
    rb : conf r c < length (tr r)
    rb = conf-bounded r c

    gox : length (tr l) + conf r c < length (tr l) + length (tr r)
    gox = <-cong (length (tr l)) rb

    go : length (tr l) + conf r c < length (tr l ⁺++⁺ tr r)
    go rewrite length-⁺++⁺ (tr l) (tr r) = gox

conf-bounded-choice-left : ∀ {A}
  → (D : F)
  → (l r : 2ADT A)
  → (c : Conf₂)
  → c D ≡ true
  → conf (D ⟨ l , r ⟩) c < length (tr l)
conf-bounded-choice-left D l r c x with c D
... | true = conf-bounded l c

-- different : Rel Selection 0ℓ
-- different (A ↣ _) (B ↣ _) = False (A == B)

-- Unique : Path → Set
-- Unique = AllPairs different

-- record UniqueList {ℓ} (A : Set ℓ) (_≟_ : DecidableEquality A) : Set ℓ where
--   field
--     list : List A
--     unique : AllPairs (λ a b → False (a ≟ b)) list

-- _∉_ : F → Path → Set
-- D ∉ p = Unique (D ↣ true ∷ p)

-- data _∈_ : Selection → Path → Set where
--   here : ∀ {p a}
--     → a ∈ (a ∷ p)

--   there : ∀ {p a b}
--     → a ∈ p
--       -----------
--     → a ∈ (b ∷ p)

-- data _leads-to_within_ : ∀ {A} → Path → ℕ → 2ADT A → Set where
--   end : ∀ {A} {v : V A}
--     → [] leads-to 0 within leaf v

--   go-left : ∀ {A} {D} {l r : 2ADT A} {n} {p : Path}
--     → D ∉ p
--     → p leads-to n within l
--       ----------------------------------------------
--     → (D ↣ true ∷ p) leads-to n within (D ⟨ l , r ⟩)

--   go-right : ∀ {A} {D} {l r : 2ADT A} {n} {p : Path}
--     → D ∉ p
--     → p leads-to n within r
--       -----------------------------------------------------------------
--     → (D ↣ false ∷ p) leads-to (length (tr l) + n) within (D ⟨ l , r ⟩)

--   go-left-forced : ∀ {A} {D} {l r : 2ADT A} {n} {p : Path}
--     → (D ↣ true) ∈ p
--     → p leads-to n within l
--       --------------------------------------------------
--     → p leads-to n within (D ⟨ l , r ⟩)

--   go-right-forced : ∀ {A} {D} {l r : 2ADT A} {n} {p : Path}
--     → (D ↣ false) ∈ p
--     → p leads-to n within r
--       --------------------------------------------------
--     → p leads-to (length (tr l) + n) within (D ⟨ l , r ⟩)

-- -- data Optimal : ∀ {A} → List F → 2ADT A → Set where
-- --   o-leaf : ∀ {A} {v : V A}
-- --     → Optimal (leaf v)

-- --   o-choice : ∀ {A} {D} {l r : 2ADT A}
-- --     → Optimal (D ⟨ l , r ⟩)

-- lookup : Path → Conf₂
-- lookup [] D = true
-- lookup ((D' ↣ b) ∷ p) D with D == D'
-- ... | yes p = b
-- ... | no ≠p = lookup p D

-- path-to-conf₂ : ∀ {A} (e : 2ADT A) (p : Path) (n : ℕ)
--   → p leads-to n within e
--   → Conf₂
-- path-to-conf₂ (leaf v) .[] .0 end = λ _ → true
-- path-to-conf₂ (D ⟨ l , r ⟩) .((D ↣ true) ∷ _) n (go-left x x₁) D' = {!!}
-- path-to-conf₂ (D ⟨ l , r ⟩) .((D ↣ false) ∷ _) .(length (tr l) + _) (go-right x x₁) D' = {!!}
-- path-to-conf₂ (D ⟨ l , r ⟩) p n (go-left-forced x x₁) D' = {!!}
-- path-to-conf₂ (D ⟨ l , r ⟩) p .(length (tr l) + _) (go-right-forced x x₁) D' = {!!}

mutual
  preservation-conf : ∀ {A : 𝔸}
    → (D : F) (l r : 2ADT A)
    → ⟦ D ⟨ l , r ⟩ ⟧₂ ⊆[ conf (D ⟨ l , r ⟩) ] ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ
  preservation-conf D l r c with c D
  ... | true  =
    begin
      ⟦ l ⟧₂ c
    ≡⟨ proj₁ (preservation-by l) c ⟩
      ⟦ tr l ⟧ₗ (conf l c)
    ≡˘⟨ append-preserves (tr l) (tr r) (conf-bounded l c) ⟩
      ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conf l c)
    ∎
  ... | false =
    begin
      ⟦ r ⟧₂ c
    ≡⟨ proj₁ (preservation-by r) c ⟩
      ⟦ tr r ⟧ₗ (conf r c)
    ≡˘⟨ prepend-preserves (conf r c) (tr l) (tr r) ⟩
      ⟦ tr l ⁺++⁺ tr r ⟧ₗ (length (tr l) + conf r c)
    ∎

  fnoc : ∀ {A} → 2ADT A → ℕ → Conf₂
  fnoc (leaf _) _ = dont-care
    where
      dont-care = λ _ → true -- does not matter what we return here
  fnoc (D ⟨ l , r ⟩) i D' =
    let sm = i ≤ᵇ length (tr l) in
    if does (D == D')
    then sm
    else if sm
         then fnoc l i D'
         else fnoc l (i ∸ (length (tr l))) D'
  -- fnoc (D ⟨ l , r ⟩) i D' with D == D' | i ≤ᵇ length (tr l)
  -- ... | yes p | left? = left?
  -- ... | no ¬p | true  = fnoc l i D'
  -- ... | no ¬p | false = fnoc l (i ∸ (length (tr l))) D'

  drefl : ∀ (D : F) → does (D == D) ≡ true
  drefl D = {!!}

  preservation-fnoc : ∀ {A : 𝔸}
    → (D : F) (l r : 2ADT A)
    → ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ ⊆[ fnoc (D ⟨ l , r ⟩) ] ⟦ D ⟨ l , r ⟩ ⟧₂
  preservation-fnoc D l r i with i ≤ᵇ length (tr l)
  ... | false = {!!}
  ... | true rewrite drefl D = {!!}
    -- begin
    --   find-or-last i (tr l ⁺++⁺ tr r)
    -- ≡⟨ ? ⟩
    --   find-or-last i (tr l)
    -- ≡⟨ proj₂ (preservation-by l) ? ⟩
    --   ⟦ l ⟧₂ (λ D' → if does (D == D') then true else fnoc l i D')
    -- ∎
  -- ... | no ¬p = ⊥-elim (¬p refl)
  -- ... | yes p with fnoc (D ⟨ l , r ⟩) i D | i ≤ᵇ length (tr l)
  -- ... | true | false = {!!}
  -- ... | true | true  = {!!}
  -- ... | false | false = {!!}
  -- ... | false | true  = {!!}
  -- with D == D' | i ≤ᵇ length (tr l)
  -- ... | a | b = ?

  preservation-by : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ e ⟧₂ ≅[ conf e ][ fnoc e ] ⟦ tr e ⟧ₗ
  preservation-by e@(leaf v) = irrelevant-index-≅ v (λ _ → refl) (λ _ → refl) (conf e) (fnoc e)
  preservation-by (D ⟨ l , r ⟩) = preservation-conf D l r , preservation-fnoc D l r

preservation : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ e ⟧₂ ≅ ⟦ tr e ⟧ₗ
preservation e = ≅[]→≅ (preservation-by e)

-- data _∈_at_ : ∀ {A} → V A → 2ADT A → ℕ → Set where
--   end : ∀ {A} {v : V A}
--       ----------------
--     → v ∈ leaf v at 0

--   go-left : ∀ {A} {D} {l r : 2ADT A} {n} {v : V A}
--     → v ∈ l at n
--       ----------------------
--     → v ∈ (D ⟨ l , r ⟩) at n

--   go-right : ∀ {A} {D} {l r : 2ADT A} {m} {v : V A}
--     → v ∈ r at m
--       ----------------------------------------
--     → v ∈ (D ⟨ l , r ⟩) at (length (tr l) + m)
