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
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Level using (0ℓ)
open import Function using (id; _∘_; _$_)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)

open import Data.EqIndexedSet hiding (Index; _∈_)
open Data.EqIndexedSet.≅-Reasoning

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
open import Util.List using (find-or-last; length-⁺++⁺; append-preserves; prepend-preserves; prepend-preserves')
open import Util.AuxProofs using (<-cong-+ˡ)
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
∉→All-different : ∀ {D} → (as : Path) → D ∉ as → All (different (D ↣ true)) as
∉→All-different [] _ = []
∉→All-different (a ∷ as) nope =
    fromWitnessFalse (λ x → nope (here (fromWitness x)))
  ∷ ∉→All-different as λ x → nope (there x)

All-different→∉ : ∀ {D} (b : Bool) (as : Path) → All (different (D ↣ b)) as → D ∉ as
All-different→∉ b (a ∷ as) (pa ∷ pas) (here D-is-a) = toWitnessFalse pa (toWitness D-is-a)
All-different→∉ b (a ∷ as) (pa ∷ pas) (there D∈as)  = All-different→∉ b as pas D∈as

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
data _starts-at_ : ∀ {A} → (p : Path) → (e : 2ADT A) → Set where
  -- any unique path is total for a leaf.
  tleaf : ∀ {A} {v : V A}
      ------------------
    → _starts-at_ [] (leaf v)

  -- We actually dont need to store the selections here.
  -- _starts-at_ itself is already a list that tells us where to
  -- go left or right. So we do not need to store that information
  -- in the path, too.
  -- Let's keep it for now because it might be easier to convert configurations as
  -- functions to paths and vice versa later on.
  walk-left : ∀ {A} {D : F} {l r : 2ADT A} {pl : Path}
    → _starts-at_ pl l
      -------------------------------------
    → _starts-at_ ((D ↣ true) ∷ pl) (D ⟨ l , r ⟩)

  walk-right : ∀ {A} {D : F} {l r : 2ADT A} {pr : Path}
    → _starts-at_ pr r
      --------------------------------------
    → _starts-at_ ((D ↣ false) ∷ pr) (D ⟨ l , r ⟩)

record TConf {A} (e : 2ADT A) : Set where
  constructor _is-total_
  field
    path : Path
    total : _starts-at_ path e
open TConf public

-- semantics by walking a path
-- this may walk illegally by choosing different alternatives for the same choice within a path
-- For example in D ⟨ D ⟨ 1 , dead ⟩ , 2 ⟩ we can reach dead via (D ↣ true ∷ D ↣ false ∷ []).
-- This method behaves well though when the path is unique and total.
walk : ∀ {A} → (e : 2ADT A) → TConf e → V A
walk (leaf v) ([] is-total tleaf) = v
walk (D ⟨ l , _ ⟩) ((.(D ↣ true ) ∷ pl) is-total walk-left  t) = walk l (pl is-total t)
walk (D ⟨ _ , r ⟩) ((.(D ↣ false) ∷ pr) is-total walk-right t) = walk r (pr is-total t)

matches : Conf₂ → Selection → Set
matches c (f ↣ val) = c f ≡ val

-- infix 10 _~_⊢_↠_ -- \rr-
infix 10 _⊢_⊑_ -- \squb=
data _⊢_⊑_ : ∀ {A} → 2ADT A → Path → Conf₂ → Set where
  end : ∀ {A} {v : V A} {c : Conf₂}
      ------------------
    → leaf v ⊢ [] ⊑ c

  go-left : ∀ {A} {Γ : Path} {c : Conf₂} {D : F} {l r : 2ADT A}
    → c D ≡ true
    → l ⊢ Γ ⊑ c
      --------------------------
    → D ⟨ l , r ⟩ ⊢ (D ↣ true ∷ Γ) ⊑ c

  go-right : ∀ {A} {Γ : Path} {c : Conf₂} {D : F} {l r : 2ADT A}
    → c D ≡ false
    → r ⊢ Γ ⊑ c
      --------------------------
    → D ⟨ l , r ⟩ ⊢ (D ↣ false ∷ Γ) ⊑ c

_⊑_ : Path → Conf₂ → Set
p ⊑ c = All (matches c) p

infix 4 _reaches_because_
record ReachableVariant (A : 𝔸) (c : Conf₂) : Set where
  constructor _reaches_because_
  field
    how  : Path
    what : V A
    that : how ⊑ c
    -- tttt : _starts-at_ how e
open ReachableVariant public

-- this evaluates an expression given a configuration and records that evaluation in terms of a path (as a side-effect)
⟦_⟧-recorded : ∀ {A} → (e : 2ADT A) → (c : Conf₂) → ReachableVariant A c
⟦ leaf v ⟧-recorded c = [] reaches v because []
⟦ D ⟨ _ , _ ⟩ ⟧-recorded c with c D in match
⟦ D ⟨ l , _ ⟩ ⟧-recorded c | true  with ⟦ l ⟧-recorded c
... | p reaches v because proof = (D ↣  true) ∷ p reaches v because match ∷ proof
⟦ D ⟨ _ , r ⟩ ⟧-recorded c | false with ⟦ r ⟧-recorded c
... | p reaches v because proof = (D ↣ false) ∷ p reaches v because match ∷ proof

{-
If we start with an empty environment. Then any selection we will put into the environment
afterwards will be dictated by the configuration function c.
Γ hence denotes a partial configuration which can be extended to become c.
-}
path-denotes-partial-config : ∀ {A} {Γ : Path} {c : Conf₂} {e : 2ADT A}
  → e ⊢ Γ ⊑ c
  → Γ ⊑ c
path-denotes-partial-config end = []
path-denotes-partial-config (go-left  c-says-so p) = c-says-so ∷ path-denotes-partial-config p
path-denotes-partial-config (go-right c-says-so p) = c-says-so ∷ path-denotes-partial-config p


-- Conf₂ → Path
conf-to-path : ∀ {A} (e : 2ADT A) (c : Conf₂) → ∃[ p ] (e ⊢ p ⊑ c)
conf-to-path (leaf v) _ = [] , end
conf-to-path (D ⟨ _ , _ ⟩) c with c D in eq
conf-to-path (D ⟨ l , _ ⟩) c | true  with conf-to-path l c
... | Γ , nice = D ↣ true  ∷ Γ , go-left  eq nice
conf-to-path (D ⟨ _ , r ⟩) c | false with conf-to-path r c
... | Γ , nice = D ↣ false ∷ Γ , go-right eq nice

get-variant : ∀ {A} {e : 2ADT A} {c : Conf₂} {p : Path} → e ⊢ p ⊑ c → V A
get-variant (end {v = v}) = v
get-variant (go-left _ pl) = get-variant pl
get-variant (go-right _ pr) = get-variant pr


path-to-conf : (p : Path) → ∃[ c ] (p ⊑ c)
path-to-conf [] = (λ _ → true) , []
path-to-conf ((D ↣ b) ∷ ps) = check-D , matches-head ∷ {!proj₂ rec!}
  where
    rec : ∃[ c ] (ps ⊑ c)
    rec = path-to-conf ps

    check-D : Conf₂
    check-D D' with D == D'
    ... | yes eq = b
    ... | no neq = proj₁ rec D'

    matches-head : matches check-D (D ↣ b)
    matches-head with D == D
    ... | yes eq = refl
    ... | no neq = ⊥-elim (neq refl)

Live : Path → Set
Live = Unique



-- module Test (a b c d : F) where
--   open import Data.String using (String)
--   module _ (with-a dead wout-a : V String) where
--     e : 2ADT String
--     e = a ⟨ a ⟨ leaf with-a , leaf dead ⟩ , leaf wout-a ⟩

--     all-yes : Conf₂
--     all-yes _ = true

--     -- this shows that a path might contain duplicates
--     -- however, these will never conflict
--     _ : ((a ↣ true) ∷ (a ↣ true) ∷ []) ~ all-yes ⊢ e ↠ with-a
--     _ = go-left refl (go-left refl end)



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
    uuu _ = ∉→All-different above D∉above ∷ u
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

toVariantList : ∀ {A : 𝔸} → 2ADT A → VariantList A
toVariantList = tr-unique ∘ ordinary-to-unique

-- leaf-count : ∀ {A : 𝔸} → 2ADT A → ℕ
-- leaf-count (leaf _) = 1
-- leaf-count (D ⟨ l , r ⟩) = leaf-count l + leaf-count r

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
    gox = <-cong-+ˡ (length trl) rb

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


module WalkToList where
  conff : ∀ {A} → (e : 2ADT A) → TConf e → ℕ
  conff .(leaf _) (.[] is-total tleaf) = 0
  conff (D ⟨ l , _ ⟩) ((_ ∷ pl) is-total walk-left  t) = conff l (pl is-total t)
  conff (D ⟨ l , r ⟩) ((_ ∷ pr) is-total walk-right t) = length (tr l) + conff r (pr is-total t)

  ffnoc : ∀ {A} → (e : 2ADT A) → ℕ → TConf e
  ffnoc (leaf v) _ = [] is-total tleaf
  ffnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
  ffnoc (D ⟨ l , r ⟩) i | no _ {-left-} with ffnoc l i
  ... | pl is-total tl = ((D ↣ true) ∷ pl) is-total walk-left tl
  ffnoc (D ⟨ l , r ⟩) i | yes _  {-right-} with ffnoc r (i ∸ (length (tr l)))
  ... | pr is-total tr = ((D ↣ false) ∷ pr) is-total walk-right tr

  preservation-walk-to-list-conf : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → walk e ⊆[ conff e ] ⟦ tr e ⟧ₗ
  preservation-walk-to-list-conf .(leaf _) (.[] is-total tleaf) = refl
  preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pl) is-total walk-left  t) =
    begin
      walk l (pl is-total t)
    ≡⟨ preservation-walk-to-list-conf l (pl is-total t) ⟩
      ⟦ tr l ⟧ₗ (conff l (pl is-total t))
    ≡˘⟨ append-preserves (tr l) (tr r) {!!} ⟩ -- we need a version of conf-bounded for conff here.
    -- ≡˘⟨ append-preserves (tr l) (tr r) (conf-bounded l c) ⟩
      ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conff l (pl is-total t))
    ∎
  preservation-walk-to-list-conf (D ⟨ _ , r ⟩) ((_ ∷ _) is-total walk-right t) = {!!} -- this should be quite similar the walk-right case for ffnoc.

  preservation-walk-to-list-fnoc : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ tr e ⟧ₗ ⊆[ ffnoc e ] walk e
  preservation-walk-to-list-fnoc (leaf v) i = refl
  preservation-walk-to-list-fnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
  ... | no ¬p =
    begin
      ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
    ≡⟨⟩
      find-or-last i ((tr l) ⁺++⁺ (tr r))
    ≡⟨ append-preserves (tr l) (tr r) (≰⇒> ¬p) ⟩ -- this is satisfied by eq
      find-or-last i (tr l)
    ≡⟨⟩
      ⟦ tr l ⟧ₗ i
    ≡⟨ preservation-walk-to-list-fnoc l i ⟩
      walk l (path (ffnoc l i) is-total total (ffnoc l i))
    ∎
  ... | yes p  =
    begin
      ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
    ≡⟨⟩
      find-or-last i ((tr l) ⁺++⁺ (tr r))
    ≡⟨ {!prepend-preserves !} ⟩
      find-or-last (i ∸ length (tr l)) (tr r)
    ≡⟨⟩
      ⟦ tr r ⟧ₗ (i ∸ length (tr l))
    ≡⟨ preservation-walk-to-list-fnoc r (i ∸ length (tr l)) ⟩
      walk r (path (ffnoc r (i ∸ length (tr l))) is-total total (ffnoc r (i ∸ length (tr l))))
    ∎

  -- When equipped with walk semantics, 2ADTs are isomorphic to lists of variants,
  -- This proof is almost done and just requires some juggling with ≤ and so on.
  preservation-walk-to-list : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → walk e ≅ ⟦ tr e ⟧ₗ
  preservation-walk-to-list e = ≅[]→≅ (preservation-walk-to-list-conf e , preservation-walk-to-list-fnoc e)

{-
If we walk a path (with walk semantics), this yields the same variant
as long as the path does not contain conflicts.
However, there might be conflicting paths: Paths that end in dead branches.
Hence, in a 2ADT without dead branches, walking a path randomly is always fine.
-}
module NoConflictWalk where
  fun-to-path : ∀ {A} (e : 2ADT A) → Conf₂ → TConf e
  fun-to-path (leaf _) _ = [] is-total tleaf
  fun-to-path (D ⟨ _ , _ ⟩) c with c D
  fun-to-path (D ⟨ l , _ ⟩) c | true  with fun-to-path l c
  ... | pl is-total tl = ((D ↣ true)  ∷ pl) is-total walk-left tl
  fun-to-path (D ⟨ _ , r ⟩) c | false with fun-to-path r c
  ... | pr is-total tr = ((D ↣ false) ∷ pr) is-total walk-right tr

  path-to-fun : ∀ {A} (e : 2ADT A) → TConf e → Conf₂
  path-to-fun .(leaf _) ([] is-total tleaf) _ = true
  path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .true) ∷ p) is-total walk-left t) D' with D == D'
  ... | yes _ = true
  ... | no  _ = path-to-fun l (p is-total t) D'
  path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .false) ∷ p) is-total walk-right t) D' with D == D'
  ... | yes _ = false
  ... | no  _ = path-to-fun r (p is-total t) D'

  path-to-fun-abstieg-l : ∀ {A}
    → {above : Path}
    → (D : F)
    → (l r : 2ADT A)
    → D ∉ above
    → UniquePaths ((D ↣ true) ∷ above) l
    → (p : Path)
    → (t : _starts-at_ p l)
    → ⟦ l ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-total walk-left t))
    ≡ ⟦ l ⟧₂ (path-to-fun      l        (            p  is-total           t))
  path-to-fun-abstieg-l D (leaf x) _ _ _ _ _ = refl
  path-to-fun-abstieg-l D (D' ⟨ a , b ⟩) r D∉above (ochc D'∉above u-a u-b) (.(D' ↣ true) ∷ pl) (walk-left t) with D == D'
  path-to-fun-abstieg-l D (D' ⟨ a , b ⟩) r D∉above (ochc D'∉above u-a u-b) (.(D' ↣ true) ∷ pl) (walk-left t) | yes D≡D' = ⊥-elim (D'∉above (here (fromWitness (sym D≡D'))))
  path-to-fun-abstieg-l D (D' ⟨ a , b ⟩) r D∉above (ochc D'∉above u-a u-b) (.(D' ↣ true) ∷ pl) (walk-left t) | no  D≢D' with D' == D'
  ... | yes D'≡D' = {!!}
  ... | no  D'≢D' = {!!}

    -- with path-to-fun (D ⟨ D' ⟨ a , b ⟩ , r ⟩) (((D ↣ true) ∷ (D' ↣ true) ∷ pl) is-total walk-left (walk-left t)) D'
    -- begin
    --   ⟦ D' ⟨ a , b ⟩ ⟧₂ (path-to-fun (D ⟨ D' ⟨ a , b ⟩ , r ⟩) (((D ↣ true) ∷ (D' ↣ true) ∷ pl) is-total walk-left (walk-left t)))
    -- ≡⟨ {!!} ⟩
    --   ⟦ D' ⟨ a , b ⟩ ⟧₂ (path-to-fun (D' ⟨ a , b ⟩) (((D' ↣ true) ∷ pl) is-total walk-left t))
    -- ∎
  path-to-fun-abstieg-l D (D' ⟨ a , b ⟩) r D∉above (ochc D'∉above u-a u-b) .((D' ↣ false) ∷ _) (walk-right t) = {!!}

  --- TODO: Define this recusively?
  path-to-fun' : ∀ {A} (e : 2ADT A) → TConf e → Conf₂
  path-to-fun' _ (p is-total t) D with D ∈? p
  ... | yes D∈p = getValue D∈p
  ... | no  D∉p = true

-- TODO: Reformulate Uniqueness as:
  Undead : ∀ {A} (e : 2ADT A) → Set
  Undead e = ∀ (p : Path) → p starts-at e → Unique p

    -- → D ∉ above
    -- → UniquePaths ((D ↣ true) ∷ above) l
    -- → (ax1 : D ∉ p) -- We should be able to compute this from UniquePaths
    -- → (ax2 : Unique p) -- We should be able to compute this from UniquePaths
  path-to-fun'-step-l : ∀ {A} {above : Path}
    → (D : F) (l r : 2ADT A)
    → Undead (D ⟨ l , r ⟩)
    → (p : Path)
    → (t : p starts-at l)
    →   ⟦ l ⟧₂ (path-to-fun' (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-total walk-left t))
      ≡ ⟦ l ⟧₂ (path-to-fun' l (p is-total t))
  path-to-fun'-step-l D l r undead p t with D ∈? p
  ... | yes D∈p = ⊥-elim (D∉p D∈p)
    where
      allu : Unique (D ↣ true ∷ p)
      allu = undead (D ↣ true ∷ p) (walk-left t)

      D∉p : D ∉ p
      D∉p with allu
      ... | All≠D ∷ _ = All-different→∉ true p All≠D
  ... | no  D∉p = {!!}
    where
      ppp : ((D ↣ true) ∷ p) starts-at (D ⟨ l , r ⟩)
      ppp = walk-left t

      pppu : Unique ((D ↣ true) ∷ p)
      pppu = undead ((D ↣ true) ∷ p) ppp

  path-to-fun'-head : ∀ {A}
    → (D : F)
    → (l r : 2ADT A)
    → (b : Bool)
    → (p : Path)
    → (t : _starts-at_ ((D ↣ b) ∷ p) (D ⟨ l , r ⟩))
    → path-to-fun' (D ⟨ l , r ⟩) (((D ↣ b) ∷ p) is-total t) D ≡ b
  path-to-fun'-head = {!!}

  path-to-fun-l : ∀ {A}
    → (D : F)
    → (l r : 2ADT A)
    → (b : Bool)
    → (p : Path)
    → (t : _starts-at_ ((D ↣ b) ∷ p) (D ⟨ l , r ⟩))
    → path-to-fun (D ⟨ l , r ⟩) (((D ↣ b) ∷ p) is-total t) D ≡ b
  path-to-fun-l D l r .true p (walk-left t) with D == D
  ... | yes D≡D = refl
  ... | no  D≢D = ⊥-elim (D≢D refl)
  path-to-fun-l D l r .false p (walk-right t) with D == D
  ... | yes D≡D = refl
  ... | no  D≢D = ⊥-elim (D≢D refl)

  preservation-path-configs-conf : ∀ {A : 𝔸}
    → {above : Path}
    → (e : 2ADT A)
    → (u : UniquePaths above e)
    → ⟦ e ⊚ u ⟧ᵤ ⊆[ fun-to-path e ] walk e
  preservation-path-configs-conf (leaf _) _ _ = refl
  preservation-path-configs-conf (D ⟨ _ , _ ⟩) _ c with c D
  preservation-path-configs-conf (_ ⟨ l , _ ⟩) (ochc _ u-l _) c | true  with fun-to-path l c in eq
  ... | pl is-total tl =
    begin
      ⟦ l ⟧₂ c
    ≡⟨⟩
      ⟦ l ⊚ u-l ⟧ᵤ c
    ≡⟨ preservation-path-configs-conf l u-l c ⟩
      walk l (fun-to-path l c)
    ≡⟨ Eq.cong (walk l) eq ⟩
      walk l (pl is-total tl)
    ∎
  preservation-path-configs-conf (_ ⟨ _ , r ⟩) (ochc _ _ u-r) c | false with fun-to-path r c in eq
  ... | _ rewrite (sym eq) = preservation-path-configs-conf r u-r c

  preservation-path-configs-fnoc : ∀ {A : 𝔸}
    → {above : Path}
    → (e : 2ADT A)
    → (u : UniquePaths above e)
    → walk e ⊆[ path-to-fun' e ] ⟦ e ⊚ u ⟧ᵤ
  preservation-path-configs-fnoc (leaf v) oleaf (.[] is-total tleaf) = refl
  preservation-path-configs-fnoc (D ⟨ l , r ⟩) (ochc D-u u-l u-r) c@((.(D ↣ true ) ∷ p) is-total walk-left t)
    rewrite path-to-fun'-head D l r true p (walk-left t) =
    begin
      walk l (p is-total t)
    ≡⟨ preservation-path-configs-fnoc l u-l (p is-total t) ⟩
      ⟦ l ⟧₂ (path-to-fun' l (p is-total t))
    ≡⟨ {!!} ⟩ --path-to-fun'-step-l D l r D-u u-l p {!!} {!!} t ⟩
      ⟦ l ⟧₂ (path-to-fun' (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-total walk-left t))
    ∎
    -- rewrite path-to-fun-l D l r true p (walk-left t) =
    --   begin
    --     walk l (p is-total t)
    --   ≡⟨ preservation-path-configs-fnoc l u-l (p is-total t) ⟩
    --     ⟦ l ⟧₂ (path-to-fun l (p is-total t))
    --   ≡˘⟨ path-to-fun-abstieg-l D l r D-u u-l p t ⟩
    --     ⟦ l ⟧₂ (path-to-fun (D ⟨ l , r ⟩) c)
    --   ∎
--     where
--       lem : path-to-fun l (p is-total t) ≡ (λ D' → path-to-fun (D ⟨ l , r ⟩) (((D ↣ true) ∷ p) is-total walk-left t) D')
--       lem = {!!}

  -- ... | yes eq = {!!}
  -- ... | no neq = {!!}
  preservation-path-configs-fnoc (D ⟨ l , r ⟩) (ochc D-u u-l u-r) ((.(D ↣ false) ∷ p) is-total walk-right t) = {!!}

  -- Configurations can be modelled as functions or as paths.
  -- The expression is unchanged here but the configurations have to be translated.
  preservation-path-configs : ∀ {A : 𝔸}
    → (e : UniquePaths2ADT A)
    → ⟦ e ⟧ᵤ ≅ walk (node e)
  preservation-path-configs e = ≅[]→≅ (preservation-path-configs-conf (node e) (unique e) , preservation-path-configs-fnoc (node e) (unique e))

module DeadBranchElim where
  preserves-l : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ e ⟧₂ ⊆[ id ] ⟦ e ⟧₂
  preserves-l (leaf _) _ = refl
  preserves-l (D ⟨ l , r ⟩) c with c D
  ... | x = {!!}

-- !what (⟦ D ⟨ l , r ⟩ ⟧-recorded c)!
  preservation-dead-branch-elim-conf : ∀ {A : 𝔸}
    -- this path cannot be arbitrary.
    -- It has to be linked to a partial configuration somehow.
    -- We need a lemma
    --   (is : D ∈? above) → getValue is ≡ c D
    -- otherwise we could not have reached that leaf.
    → (above : Path)
    → (u : Unique above)
    -- Das Hilfslemma ist noch zu allgemein, da above immer noch magisch aus dem Nichts kommt.
    -- Nichts sagt, dass above tatsächlich ein Pfad war, den wir verfolgt haben. Brauchen wir hier auch schon _starts-at_?
    → (∀ (D : F) (fixed : D ∈ above) → (c : Conf₂) → c D ≡ getValue fixed )
    → (e : 2ADT A)
    → ⟦ e ⟧₂ ⊆[ id ] ⟦ ordinary-to-unique' above u e ⟧ᵤ
  preservation-dead-branch-elim-conf _ _ _ (leaf v) c = refl
  preservation-dead-branch-elim-conf above _ _ (D ⟨ _ , _ ⟩) _ with D ∈? above
  preservation-dead-branch-elim-conf above u lem (D ⟨ l , r ⟩) c | yes p rewrite (lem D p c) with getValue p
  ... | true  = preservation-dead-branch-elim-conf above u lem l c
  ... | false = preservation-dead-branch-elim-conf above u lem r c
  preservation-dead-branch-elim-conf above u lem (D ⟨ l , r ⟩) c | no ¬p with c D
  ... | true  = preservation-dead-branch-elim-conf ((D ↣  true) ∷ above) (∉→All-different above ¬p ∷ u) lem-step l c
    where
      lem-step : ∀ (D' : F) (fixed : D' ∈ ((D ↣ true) ∷ above)) (c : Conf₂) → c D' ≡ getValue fixed
      lem-step D' fixed c with D == D'
      ... | yes D≡D' rewrite D≡D' = {!!}
      ... | no  D≢D' = lem D' {!!} c
  ... | false = preservation-dead-branch-elim-conf ((D ↣ false) ∷ above) (∉→All-different above ¬p ∷ u) {!!} r c

  preservation-dead-branch-elim-fnoc : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ ordinary-to-unique e ⟧ᵤ ⊆[ id ] ⟦ e ⟧₂
  preservation-dead-branch-elim-fnoc = {!!}

  -- Killing dead branches is ok.
  preservation-dead-branch-elim : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ e ⟧₂ ≅ ⟦ ordinary-to-unique e ⟧ᵤ
  preservation-dead-branch-elim e = ≅[]→≅ (preservation-dead-branch-elim-conf [] [] lem-base e , preservation-dead-branch-elim-fnoc e)
    where
      lem-base : ∀ (D : F) (fixed : D ∈ []) (c : Conf₂) → c D ≡ getValue fixed
      lem-base D () c

-- 2ADTs are isomorphic to Variant Lists.
preservation : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ e ⟧₂ ≅ ⟦ toVariantList e ⟧ₗ
preservation e =
  ≅-begin
    ⟦ e ⟧₂
  ≅⟨ DeadBranchElim.preservation-dead-branch-elim e ⟩
    ⟦ ordinary-to-unique e ⟧ᵤ
  ≅⟨ NoConflictWalk.preservation-path-configs (ordinary-to-unique e) ⟩
    walk (node (ordinary-to-unique e))
  ≅⟨ WalkToList.preservation-walk-to-list (node (ordinary-to-unique e)) ⟩ -- conceptually done
    ⟦ toVariantList e ⟧ₗ
  ≅-∎

---- DEPRECATED STUFF FROM HERE ON THAT WE MIGHT NEED LATER AGAIN ----

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
