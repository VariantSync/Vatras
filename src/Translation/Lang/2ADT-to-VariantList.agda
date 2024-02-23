open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.2ADT-to-VariantList
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.NonEmpty using (List⁺; _∷_; _++⁺_; _⁺++⁺_; toList; length)
open import Data.List.NonEmpty.Properties using (length-++⁺)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤?_; _≤ᵇ_; z≤n; s≤s; s<s) --_≤?_)
open import Data.Nat.Properties using (≤-trans; ≰⇒>; <⇒≤; m≤m+n)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Level using (0ℓ)
open import Function using (_∘_)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)

open import Data.EqIndexedSet hiding (Index; _∈_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (does; proof; yes; no; False; True; fromWitness; toWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Binary using (Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Framework.VariabilityLanguage
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

-- A selection of a feature matches it to a boolean value.
record Selection : Set where
  constructor _↣_
  field
    feature : F
    value : Bool

-- A list of selection which denotes a path from the root of a 2ADT to a leaf node.
Path : Set
Path = List Selection

-- Two Selections are considered different iff they have different features.
-- Notable, (A ↣ true) is not different to (A ↣ false).
different : Rel Selection 0ℓ
different (A ↣ _) (B ↣ _) = False (A == B)

sym-different : Symmetric different
sym-different neq = fromWitnessFalse λ eq → toWitnessFalse neq (sym eq)

-- Two selections are considered the same of they assign the same feature.
same : Rel Selection 0ℓ
same (A ↣ _) (B ↣ _) = True (A == B)

-- Checks whether a given features was assigned in a selection.
is : F → Selection → Set
is A (B ↣ _) = True (A == B)

-- Checks whether a feature is assigned somewhere in a path.
_∈_ : F → Path → Set
a ∈ as = Any (is a) as

_∉_ : F → Path → Set
D ∉ fs = ¬ (D ∈ fs)

∉-head : ∀ {D x xs} → D ∉ (x ∷ xs) → (b : Bool) → different x (D ↣ b)
∉-head D∉x∷xs b = fromWitnessFalse λ x≡D → D∉x∷xs (here (fromWitness (sym x≡D)))

∉-tail : ∀ {D x xs} → D ∉ (x ∷ xs) → D ∉ xs
∉-tail D∉x∷xs D∈xs = D∉x∷xs (there D∈xs)

-- Finds the assigned value of a feature within a path.
getValue : ∀ {a fs} → a ∈ fs → Bool
getValue (here {_ ↣ value} _) = value
getValue (there fs) = getValue fs

-- Containment _∈_ is decidable.
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

-- Turns an ¬ Any to a All ¬.
-- TODO: Reuse ¬Any⇒All¬ from the standard library.
flip : ∀ {b} → (as : Path) → ¬ b ∈ as → All (different (b ↣ true)) as
flip [] _ = []
flip (a ∷ as) nope =
    fromWitnessFalse (λ x → nope (here (fromWitness x)))
  ∷ flip as λ x → nope (there x)

Unique : Path → Set
Unique = AllPairs different

-- All paths from a leaf to the root choice are unique.
-- data UniquePaths : ∀ {A} → Path → 2ADT A → Set where
--   -- At a leaf, any path of unique feature names might have ended here.
--   oleaf : ∀ {A} {v : V A} {above : Path}
--     → Unique above
--       -----------------------
--     → UniquePaths above (leaf v)

--   -- Any path 'above' can lead to a choice, when it is legal
--   -- to continue it downwards with configuring the choice.
--   ochc : ∀ {A} {D : F} {l r : 2ADT A} {above : Path}
--     → UniquePaths (above ∷ʳ (D ↣ true)) l
--     → UniquePaths (above ∷ʳ (D ↣ false)) r
--       ------------------------------------
--     → UniquePaths above (D ⟨ l , r ⟩)

data UniquePaths : ∀ {A} → Path → 2ADT A → Set where
  -- At a leaf, any path of unique feature names might have ended here.
  oleaf : ∀ {A} {v : V A} {above : Path}
      --------------------------
    → UniquePaths above (leaf v)

  -- Any path 'above' can lead to a choice, when it is legal
  -- to continue it downwards with configuring the choice.
  ochc : ∀ {A} {D : F} {l r : 2ADT A} {above : Path}
    → D ∉ above
    → UniquePaths ((D ↣ true) ∷ above) l
    → UniquePaths ((D ↣ false) ∷ above) r
      ------------------------------------
    → UniquePaths above (D ⟨ l , r ⟩)

-- up-swap : ∀ {A} {x y : Selection} {xs : Path} {e : 2ADT A} → UniquePaths (x ∷ y ∷ xs) e → UniquePaths (y ∷ x ∷ xs) e
-- up-swap (oleaf ((x ∷ xs) ∷ y ∷ zs)) = oleaf ((sym-different x ∷ y) ∷ xs ∷ zs)
-- up-swap (ochc l r ) = ochc {!!} {!!}

-- up-tail : ∀ {A} {x : Selection} {xs : Path} {e : 2ADT A} → UniquePaths (x ∷ xs) e → UniquePaths xs e
-- up-tail (oleaf (ux ∷ uxs)) = oleaf uxs
-- up-tail (ochc ul ur) = ochc (up-tail ul) (up-tail ur)

record UniquePaths2ADTBelow (above : Path) (A : 𝔸) : Set where
  constructor _⊚_ -- \oo
  field
    node   : 2ADT A
    unique : UniquePaths above node
open UniquePaths2ADTBelow public

UniquePaths2ADT : 𝔼
UniquePaths2ADT = UniquePaths2ADTBelow []

-- A path is total if it brings us from the root to a leaf
data Total : ∀ {A} → (p : Path) → (e : 2ADT A) → Set where
  -- any unique path is total for a leaf.
  tleaf : ∀ {A} {v : V A}
    → Total [] (leaf v)

  go-left : ∀ {A} {D : F} {l r : 2ADT A} {pl : Path}
    → Total pl l
    → Total ((D ↣ true) ∷ pl) (D ⟨ l , r ⟩)

  go-right : ∀ {A} {D : F} {l r : 2ADT A} {pr : Path}
    → Total pr r
    → Total ((D ↣ false) ∷ pr) (D ⟨ l , r ⟩)

record TConf {A} (e : 2ADT A) : Set where
  constructor _is-total_
  field
    path : Path
    total : Total path e
open TConf public

-- semantics by walking a path
-- this may walk illegally by choosing different alternatives for the same choice within a path
-- For example in D ⟨ D ⟨ 1 , dead ⟩ , 2 ⟩ we can reach dead via (D ↣ true ∷ D ↣ false ∷ []).
-- This method behaves well though when the path is unique and total.
walk : ∀ {A} → (e : 2ADT A) → TConf e → V A
walk (leaf v) ([] is-total tleaf) = v
walk (D ⟨ l , r ⟩) ((.(D ↣ true ) ∷ pl) is-total go-left  t) = walk l (pl is-total t)
walk (D ⟨ l , r ⟩) ((.(D ↣ false) ∷ pr) is-total go-right t) = walk r (pr is-total t)

⟦_⟧ᵤ : ∀ {above : Path} → 𝔼-Semantics V Conf₂ (UniquePaths2ADTBelow above)
⟦_⟧ᵤ = ⟦_⟧₂ ∘ node

-- semantics of UniquePaths2ADTBelow
-- It is just the semantics of the contained tree.
-- We drop the typing because we do not need it for configuring the expression.
-- ⟦_⟧ᵤ : ∀ {above : Path} {A : 𝔸} → (e : UniquePaths2ADTBelow above A) → TConf (node e) → V A
-- ⟦_⟧ᵤ = walk ∘ node

UniquePaths2ADT-VL : VariabilityLanguage V
UniquePaths2ADT-VL = ⟪ UniquePaths2ADT , Conf₂ , ⟦_⟧ᵤ ⟫

ordinary-to-unique' : ∀ {A}
  → (above : Path)
  → Unique above
  → 2ADT A
  → UniquePaths2ADTBelow above A
ordinary-to-unique' _ _ (leaf v) = leaf v ⊚ oleaf
ordinary-to-unique' {A} above u (D ⟨ l , r ⟩) with D ∈? above
--- The current choice was already encountered above this choice.
--- This means, this choice is dominated (see choice domination).
--- This in turn means, that one of the choice's alternatives is dead because it cannot
--- be selected anymore.
... | yes D∈above =
  if getValue D∈above
  then ordinary-to-unique' above u l
  else ordinary-to-unique' above u r
-- The current choice was not encountered before. We follow both paths recursively,
-- adding our choice information to each path.
... | no  D∉above = (D ⟨ node rec-l , node rec-r ⟩) ⊚ ochc D∉above (unique rec-l) (unique rec-r)
  where
    uuuu : ∀ (xs : Path) → Unique xs → ¬ (D ∈ xs) → (b : Bool) → Unique (xs ∷ʳ (D ↣ b))
    uuuu [] u notin b = [] ∷ []
    uuuu (x ∷ xs) (ux ∷ uxs) notin b = All-++⁺ first second ∷ uuuu xs uxs (∉-tail notin) b
      where
        first : All (different x) xs
        first = ux

        second : All (different x) (D ↣ b ∷ [])
        second = (∉-head notin b) ∷ []


    newlist : ∀ (b : Bool) → Path
    newlist b = (D ↣ b) ∷ above
    -- newlist : ∀ (b : Bool) → Path
    -- newlist b = above ∷ʳ (D ↣ b)

    uuu : ∀ (b : Bool) → Unique (newlist b)
    uuu _ = flip above D∉above ∷ u
    -- uuu : ∀ (b : Bool) → Unique (above ∷ʳ (D ↣ b))
    -- uuu = uuuu above u D∉above

    rec-l : UniquePaths2ADTBelow (newlist true) A
    rec-l = ordinary-to-unique' (newlist true) (uuu true) l

    rec-r : UniquePaths2ADTBelow (newlist false) A
    rec-r = ordinary-to-unique' (newlist false) (uuu false) r

ordinary-to-unique : ∀ {A} → 2ADT A → UniquePaths2ADT A
ordinary-to-unique e = ordinary-to-unique' [] [] e

unique-to-ordinary : ∀ {A} → UniquePaths2ADT A → 2ADT A
unique-to-ordinary = node

-- tr' : ∀ {A : 𝔸} {above : Path} → UniquePaths2ADTBelow above A → VariantList A
-- tr' (leaf v ⊚ _) = v ∷ []
-- tr' ((D ⟨ l , r ⟩) ⊚ ochc u-l u-r) = (tr' (l ⊚ u-l)) ⁺++⁺ (tr' (r ⊚ u-r))

tr : ∀ {A : 𝔸} → 2ADT A → VariantList A
tr (leaf v) = v ∷ []
tr (D ⟨ l , r ⟩) = tr l ⁺++⁺ tr r

tr-unique : ∀ {A : 𝔸} → UniquePaths2ADT A → VariantList A
tr-unique = tr ∘ node

-- leaf-count : ∀ {A : 𝔸} → 2ADT A → ℕ
-- leaf-count (leaf _) = 1
-- leaf-count (D ⟨ l , r ⟩) = leaf-count l + leaf-count r

open import Data.List.Properties using (length-++)
length-⁺++⁺ : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A)
  → length (xs ⁺++⁺ ys) ≡ length xs + length ys
length-⁺++⁺ (x ∷ xs) (y ∷ ys) = length-++ (x ∷ xs)

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
... | true = conf l c
... | false = length (tr l) + conf r c

-- conf-unique : ∀ {A} {above : Path} → UniquePaths2ADTBelow above A → Conf₂ → ℕ
-- conf-unique (leaf v ⊚ _) c = 0
-- conf-unique ((D ⟨ l , r ⟩) ⊚ ochc u-l u-r) c =
--   let
--     rec-l = l ⊚ u-l
--     rec-r = r ⊚ u-r
--   in
--     if c D
--     then conf-unique rec-l c
--     else length (tr' rec-l) + conf-unique rec-r c

conf-unique : ∀ {A} {above : Path} → UniquePaths2ADTBelow above A → Conf₂ → ℕ
conf-unique = conf ∘ node

-- TODO: Rewrite for conff
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
    trl = tr l
    trr = tr r

    rb : conf r c < length trr
    rb = conf-bounded r c

    gox : length trl + conf r c < length trl + length trr
    gox = <-cong (length trl) rb

    go : length trl + conf r c < length (trl ⁺++⁺ trr)
    go rewrite length-⁺++⁺ trl trr = gox

conf-unique-bounded : ∀ {A}
  → (e : UniquePaths2ADT A)
  → (c : Conf₂)
  → conf-unique e c < length (tr-unique e)
conf-unique-bounded = conf-bounded ∘ node

-- conf-unique-bounded-choice-left : ∀ {A}
--   → (D : F)
--   → (l r : 2ADT A)
--   → (c : Conf₂)
--   → c D ≡ true
--   → conf-unique (D ⟨ l , r ⟩) c < length (tr-unique l)
-- conf-unique-bounded-choice-left D l r c x with c D
-- ... | true = conf-unique-bounded l c

preservation-conf : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ e ⟧₂ ⊆[ conf e ] ⟦ tr e ⟧ₗ
preservation-conf e@(leaf v) = irrelevant-index-⊆ v (λ _ → refl) (λ _ → refl) (conf e)
preservation-conf (D ⟨ l , r ⟩) c with c D
... | true  =
  begin
    ⟦ l ⟧₂ c
  ≡⟨ preservation-conf l c ⟩
    ⟦ tr l ⟧ₗ (conf l c)
  ≡˘⟨ append-preserves (tr l) (tr r) (conf-bounded l c) ⟩
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conf l c)
  ∎
... | false =
  begin
    ⟦ r ⟧₂ c
  ≡⟨ preservation-conf r c ⟩
    ⟦ tr r ⟧ₗ (conf r c)
  ≡˘⟨ prepend-preserves (conf r c) (tr l) (tr r) ⟩
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (length (tr l) + conf r c)
  ∎

-- fnoc (D ⟨ l , r ⟩) i D' with D == D' | i ≤ᵇ length (tr-unique l)
-- ... | yes p | left? = left?
-- ... | no ¬p | true  = fnoc l i D'
-- ... | no ¬p | false = fnoc l (i ∸ (length (tr-unique l))) D'

-- preservation-fnoc : ∀ {A : 𝔸}
--   → (D : F) (l r : 2ADT A)
--   → ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ ⊆[ fnoc (D ⟨ l , r ⟩) ] ⟦ D ⟨ l , r ⟩ ⟧₂
-- preservation-fnoc D l r i = ?

-- We need this indirection that splits up a UniquePaths2ADTBelow for termination checking.
-- fnoc-unique' : ∀ {A} {above : Path} → (e : 2ADT A) → UniquePaths above e → ℕ → Conf₂
-- fnoc-unique' (leaf x) _ _ _ = true -- don't care
-- fnoc-unique' (D ⟨ l , r ⟩) (ochc u-l u-r) i D' = {!!}

-- find-path-to : ∀ {A} {above : Path} → (e : 2ADT A) → UniquePaths above e → ℕ → Σ Path Unique
-- find-path-to (leaf v) u i = [] , []
-- find-path-to (D ⟨ l , r ⟩) (ochc u-l u-r) i with length (tr l) ≤ᵇ i
-- ... | false {-left-} =
--   let
--     ll = find-path-to l u-l i
--   in
--     (D ↣ true) ∷ proj₁ ll , {!u-l!} ∷ {!!}
-- ... | true  = {!!}

-- fnoc-unique' : ∀ {A} {above : Path} → (e : 2ADT A) → UniquePaths above e → ℕ → Conf₂
-- fnoc-unique' (leaf x) _ _ _ = true -- don't care
-- fnoc-unique' (D ⟨ l , r ⟩) (ochc u-l u-r) i D' with i ≤ᵇ length (tr l) | D == D'
-- ... | true  | yes p = true
-- ... | false | yes p = false
-- ... | true  | no ¬p = fnoc-unique' l u-l i D'
-- ... | false | no ¬p = fnoc-unique' l u-l (i ∸ (length (tr l))) D'
-- fnoc-unique' (D ⟨ l , r ⟩) (ochc u-l u-r) i D' with D == D' | i ≤ᵇ length (tr l)
-- ... | yes p | left? = left?
-- ... | no ¬p | true  = fnoc-unique' l u-l i D'
-- ... | no ¬p | false = fnoc-unique' l u-l (i ∸ (length (tr l))) D'

-- fnoc-unique : ∀ {A} {above : Path} → UniquePaths2ADTBelow above A → ℕ → Conf₂
-- fnoc-unique (e ⊚ u) = fnoc-unique' e u

-- fnoc (leaf _) _ _ = true -- dont care
-- fnoc (D ⟨ l , r ⟩) i D' with D == D' | i ≤ᵇ length (tr l)
-- ... | yes p | left? = left?
-- ... | no ¬p | true  = fnoc l i D'
-- ... | no ¬p | false = fnoc l (i ∸ (length (tr l))) D'

-- fnoc (leaf _) _ = dont-care
--   where
--     dont-care = λ _ → true -- does not matter what we return here
-- fnoc (D ⟨ l , r ⟩) i D' =
--   let sm = i ≤ᵇ length (tr l) in
--   if does (D == D')
--   then sm
--   else if sm
--         then fnoc l i D'
--         else fnoc l (i ∸ (length (tr l))) D'

-- mutual
  -- preservation-fnoc-unique : ∀ {A : 𝔸} {above : Path}
  --     → (e : UniquePaths2ADTBelow above A)
  --     → ⟦ tr (node e) ⟧ₗ ⊆[ fnoc-unique e ] ⟦ e ⟧ᵤ
  -- preservation-fnoc-unique (leaf _ ⊚ _) _ = refl
  -- preservation-fnoc-unique ((D ⟨ l , r ⟩) ⊚ u) i with i ≤ᵇ length (tr l)
  -- ... | false = {!!}
  -- ... | true  = {!!}
    -- begin
    --   ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
    -- ≡⟨⟩
    --   (find-or-last i ((tr l) ⁺++⁺ (tr r)))
    -- ≡⟨⟩
    --   (find-or-last i (List⁺.head (tr l) ∷ tail (tr l) ++ List⁺.head (tr r) ∷ tail (tr r)))
    -- ≡⟨ {!!} ⟩
    --   (if c D then ⟦ l ⟧₂ c else ⟦ r ⟧₂ c)
    -- ≡⟨⟩
    --   ⟦ D ⟨ l , r ⟩ ⟧₂ c
    -- ∎

conff : ∀ {A} → (e : 2ADT A) → TConf e → ℕ
conff .(leaf _) (.[] is-total tleaf) = 0
conff (D ⟨ l , _ ⟩) ((_ ∷ pl) is-total go-left  t) = conff l (pl is-total t)
conff (D ⟨ l , r ⟩) ((_ ∷ pr) is-total go-right t) = length (tr l) + conff r (pr is-total t)

ffnoc : ∀ {A} → (e : 2ADT A) → ℕ → TConf e
ffnoc (leaf v) _ = [] is-total tleaf
ffnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
ffnoc (D ⟨ l , r ⟩) i | no _ {-left-} with ffnoc l i
... | pl is-total tl = ((D ↣ true) ∷ pl) is-total go-left tl
ffnoc (D ⟨ l , r ⟩) i | yes _  {-right-} with ffnoc r (i ∸ (length (tr l)))
... | pr is-total tr = ((D ↣ false) ∷ pr) is-total go-right tr

preservation-conff : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → walk e ⊆[ conff e ] ⟦ tr e ⟧ₗ
preservation-conff .(leaf _) (.[] is-total tleaf) = refl
preservation-conff (D ⟨ l , r ⟩) ((_ ∷ pl) is-total go-left  t) =
  begin
    walk l (pl is-total t)
  ≡⟨ preservation-conff l (pl is-total t) ⟩
    ⟦ tr l ⟧ₗ (conff l (pl is-total t))
  ≡˘⟨ append-preserves (tr l) (tr r) {!!} ⟩
  -- ≡˘⟨ append-preserves (tr l) (tr r) (conf-bounded l c) ⟩
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conff l (pl is-total t))
  ∎
preservation-conff (D ⟨ _ , r ⟩) ((_ ∷ _) is-total go-right t) = {!!}

preservation-ffnoc : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ tr e ⟧ₗ ⊆[ ffnoc e ] walk e
preservation-ffnoc (leaf v) i = refl
preservation-ffnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
... | no ¬p =
  begin
    ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
  ≡⟨⟩
    find-or-last i ((tr l) ⁺++⁺ (tr r))
  ≡⟨ append-preserves (tr l) (tr r) (≰⇒> ¬p) ⟩ -- this is satisfied by eq
    find-or-last i (tr l)
  ≡⟨⟩
    ⟦ tr l ⟧ₗ i
  ≡⟨ preservation-ffnoc l i ⟩
    walk l (path (ffnoc l i) is-total total (ffnoc l i))
  ∎
... | yes p  =
  begin
    ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
  ≡⟨⟩
    find-or-last i ((tr l) ⁺++⁺ (tr r))
  ≡⟨ {!!} ⟩
    ⟦ tr r ⟧ₗ (i ∸ length (tr l))
  ≡⟨ preservation-ffnoc r (i ∸ length (tr l)) ⟩
    walk r (path (ffnoc r (i ∸ length (tr l))) is-total total (ffnoc r (i ∸ length (tr l))))
  ∎

preservation : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → walk e ≅ ⟦ tr e ⟧ₗ
preservation e = ≅[]→≅ (preservation-conff e , preservation-ffnoc e)
