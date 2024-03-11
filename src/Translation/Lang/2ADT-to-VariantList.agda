open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
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
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (0ℓ)
open import Function using (id; _∘_; _$_)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)

open import Data.EqIndexedSet hiding (Index; _∈_)
open Data.EqIndexedSet.≅-Reasoning

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (does; proof; yes; no; False; True; isYes; isNo; fromWitness; toWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Binary using (Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Framework.VariabilityLanguage
open import Lang.2ADT F V
  using (2ADT; 2ADTL; leaf; _⟨_,_⟩)
  renaming (⟦_⟧ to ⟦_⟧₂; Configuration to Conf₂)
open import Lang.VariantList V
  using (VariantList; VariantListL)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Confₗ)
open import Framework.Relation.Expressiveness V using (_≽_; expressiveness-by-translation)

-- imports for nicer holes
open import Util.List using (find-or-last; ⁺++⁺-length; ⁺++⁺-length-≤; append-preserves; prepend-preserves-+; prepend-preserves-∸)
open import Util.AuxProofs using (<-cong-+ˡ; if-cong)
open import Util.Suffix
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

is-refl : ∀ (D : F) → (b : Bool) → is D (D ↣ b)
is-refl _ _ = fromWitness refl

==-isYes-refl : ∀ (D : F) → isYes (D == D) ≡ true
==-isYes-refl D with D == D
... | yes refl = refl
... | no D≠D = ⊥-elim (D≠D refl)

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

{-
All features mentioned in the path are unique (i.e., no feature is mentioned more than once).
This means that there cannot be conflicts in the path.
-}
Unique : Path → Set
Unique = AllPairs different

{-
A path is starts at a node if it leads to a leaf.
This relation can be seen as a type system for paths within a particular tree.
Note: The symmetry between the rules walk-left and walk-right causes many
      proofs to have quite some redundancy as well because we have to match
      on these rules a lot.
      However, we cannot merge the rules into a single rule
      because we have to recurse on either the left or right alternative (not both).
-}
data _starts-at_ : ∀ {A} → (p : Path) → (e : 2ADT A) → Set where
  tleaf : ∀ {A} {v : V A}
      ------------------
    → [] starts-at (leaf v)

  walk-left : ∀ {A} {D : F} {l r : 2ADT A} {pl : Path}
    → pl starts-at l
      -------------------------------------
    → ((D ↣ true) ∷ pl) starts-at (D ⟨ l , r ⟩)

  walk-right : ∀ {A} {D : F} {l r : 2ADT A} {pr : Path}
    → pr starts-at r
      --------------------------------------
    → ((D ↣ false) ∷ pr) starts-at (D ⟨ l , r ⟩)

{-
An expression does not contain a feature name
if all paths do not contain that feature name.
-}
_∉'_ : ∀{A} → F → 2ADT A → Set
D ∉' e = ∀ (p : Path) → p starts-at e → D ∉ p

{-
A path serves as a configuration for an expression e
if it starts at that expression and ends at a leaf.
-}
record PathConfig {A} (e : 2ADT A) : Set where
  constructor _is-valid_
  field
    path : Path
    valid : path starts-at e
open PathConfig public

{-
Alternative semantics of 2ADTs by walking a path.
This walk may be illegal by choosing different alternatives for the same choice within a path.
For example in D ⟨ D ⟨ 1 , dead ⟩ , 2 ⟩ we can reach 'dead' via (D ↣ true ∷ D ↣ false ∷ []).
However, walking like this is fine as long as the path is unique as we will later prove.
-}
walk : ∀ {A} → (e : 2ADT A) → PathConfig e → V A
walk (leaf v) ([] is-valid tleaf) = v
walk (D ⟨ l , _ ⟩) ((.(D ↣ true ) ∷ pl) is-valid walk-left  t) = walk l (pl is-valid t)
walk (D ⟨ _ , r ⟩) ((.(D ↣ false) ∷ pr) is-valid walk-right t) = walk r (pr is-valid t)

{-
An expression a is a sub-expression of b
iff all valid paths from a lead to paths from b.
-}
_subexprof_ : ∀ {A} → 2ADT A → 2ADT A → Set
a subexprof b = ∀ (pa : Path) → pa starts-at a → ∃[ pb ] ((pb starts-at b) × (pb endswith pa))

{-
A configuration matches a selection
if the configuration returns the same
result for the given feature as dictated
by the selection.
-}
matches : Conf₂ → Selection → Set
matches c (f ↣ val) = c f ≡ val

{-
Predicate that tells whether a path matches a configuration.
This essentially makes the given path a partial configuration.
-}
_⊑_ : Path → Conf₂ → Set
p ⊑ c = All (matches c) p

{-
If we make a lookup in a path for a certain feature,
any matching configuration will yield the same result.
-}
lookup-partial : ∀ {p} {c} {D}
  → p ⊑ c
  → (has : D ∈ p)
  → getValue has ≡ c D
lookup-partial (refl ∷ px) (here D-is-f) rewrite toWitness D-is-f = refl
lookup-partial (refl ∷ px) (there has) = lookup-partial px has

{-
A 2ADT is undead if it does not contain any dead branches.
This is the case if any path from the root to a leaf does not contain
a feature name twice.
-}
Undead : ∀ {A} (e : 2ADT A) → Set
Undead e = ∀ (p : Path) → p starts-at e → Unique p

{-
A leaf node is always undead.
-}
undead-leaf : ∀ {A} {v : V A}
    ---------------
  → Undead (leaf v)
undead-leaf .[] tleaf = []

{-
If a choice is undead, so is its left alternative.
-}
undead-left : ∀ {A} {D} {l r : 2ADT A}
  → Undead (D ⟨ l , r ⟩)
    --------------------
  → Undead l
undead-left {D = D} u-chc p t with u-chc (D ↣ true ∷ p) (walk-left t)
... | _ ∷ u-p = u-p

{-
If a choice is undead, so is its right alternative.
-}
undead-right : ∀ {A} {D} {l r : 2ADT A}
  → Undead (D ⟨ l , r ⟩)
    --------------------
  → Undead r
undead-right {D = D} u-chc p t with u-chc (D ↣ false ∷ p) (walk-right t)
... | _ ∷ u-p = u-p

{-
If two expressions l and r are undead and do
not contain the feature name D,
then the choice D ⟨ l , r ⟩ is undead, too.
-}
undead-choice : ∀ {A} {D} {l r : 2ADT A}
  → Undead l
  → Undead r
    -- It might be handy to introduce a new predicate for containment of feature names in expressions D ∈ l later.
  → D ∉' l
  → D ∉' r
    --------------------------------------
  → Undead (D ⟨ l , r ⟩)
undead-choice u-l u-r D∉l D∉r (.(_ ↣ true ) ∷ p) (walk-left  t) = ∉→All-different p (D∉l p t) ∷ (u-l p t)
undead-choice u-l u-r D∉l D∉r (.(_ ↣ false) ∷ p) (walk-right t) = ∉→All-different p (D∉r p t) ∷ (u-r p t)

record Undead2ADT (A : 𝔸) : Set where
  constructor _⊚_ -- \oo
  field
    node   : 2ADT A
    undead : Undead node
open Undead2ADT public

⟦_⟧ᵤ : 𝔼-Semantics V Conf₂ Undead2ADT
⟦_⟧ᵤ = ⟦_⟧₂ ∘ node

Undead2ADT-VL : VariabilityLanguage V
Undead2ADT-VL = ⟪ Undead2ADT , Conf₂ , ⟦_⟧ᵤ ⟫

{-
Kills all dead branches within a given expression,
assuming that some features were already defined.
-}
kill-dead-below : ∀ {A}
  → (defined : Path)
  → 2ADT A
  → 2ADT A
kill-dead-below _ (leaf v) = leaf v
kill-dead-below defined (D ⟨ l , r ⟩) with D ∈? defined
--- The current choice was already encountered above this choice.
--- This means, this choice is dominated (see choice domination).
--- This in turn means, that one of the choice's alternatives is dead because it cannot
--- be selected anymore.
... | yes D∈defined =
  if getValue D∈defined
  then kill-dead-below defined l
  else kill-dead-below defined r
-- The current choice was not encountered before. We follow both paths recursively,
-- adding our choice information to each path.
... | no D∉defined = D ⟨ kill-dead-below (D ↣ true ∷ defined) l , kill-dead-below (D ↣ false ∷ defined) r ⟩

{-
If a feature name was already defined,
then any path starting at an expression,
in which dead branches were eliminated accordingly,
does not contain that feature name.
-}
kill-dead-eliminates-defined-features : ∀ {A}
  → (defined : Path)
  → (D : F)
  → D ∈ defined
  → (e : 2ADT A)
  → D ∉' kill-dead-below defined e
kill-dead-eliminates-defined-features _ _ _ (leaf _) .[] tleaf ()
kill-dead-eliminates-defined-features defined _ _ (D' ⟨ _ , _ ⟩) _ _ _ with D' ∈? defined
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ l , r ⟩) p t D∈p | yes D'-def with getValue D'-def
... | true  = kill-dead-eliminates-defined-features defined D D-def l p t D∈p
... | false = kill-dead-eliminates-defined-features defined D D-def r p t D∈p
kill-dead-eliminates-defined-features _ D _ (D' ⟨ _ , _ ⟩) _ _ _
  | no ¬D'-def with D == D'
kill-dead-eliminates-defined-features _ _ D-def (_  ⟨ _ , _ ⟩) _ _ _
  | no ¬D'-def | yes refl = ⊥-elim (¬D'-def D-def)
kill-dead-eliminates-defined-features _ _       _     (D' ⟨ _ , _ ⟩) ((.D' ↣ true) ∷ _) (walk-left _) (here D=D')
  | no _       | no D≠D'  = ⊥-elim (D≠D' (toWitness D=D'))
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ l , _ ⟩) ((.D' ↣ true) ∷ p) (walk-left t) (there D∈p)
  | no ¬D'-def | no D≠D'  = kill-dead-eliminates-defined-features (D' ↣ true ∷ defined) D (there D-def) l p t D∈p
kill-dead-eliminates-defined-features _ _       _     (D' ⟨ _ , _ ⟩) ((.D' ↣ false) ∷ _) (walk-right _) (here D=D')
  | no _       | no D≠D'  = ⊥-elim (D≠D' (toWitness D=D'))
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ _ , r ⟩) ((.D' ↣ false) ∷ p) (walk-right t) (there D∈p)
  | no ¬D'-def | no D≠D'  = kill-dead-eliminates-defined-features (D' ↣ false ∷ defined) D (there D-def) r p t D∈p

{-
Proof that kill-dead is correct,
which means that the resulting tree
is undead.
-}
kill-dead-correct : ∀ {A}
  → (defined : Path)
  → (e : 2ADT A)
  → Undead (kill-dead-below defined e)
kill-dead-correct _ (leaf v) = undead-leaf
kill-dead-correct defined (D ⟨ _ , _ ⟩) with D ∈? defined
kill-dead-correct defined (_ ⟨ l , r ⟩) | yes D∈defined with getValue D∈defined
... | true  = kill-dead-correct defined l
... | false = kill-dead-correct defined r
kill-dead-correct defined (D ⟨ l , r ⟩) | no  D∉defined =
  undead-choice
  (kill-dead-correct (D ↣ true  ∷ defined) l)
  (kill-dead-correct (D ↣ false ∷ defined) r)
  (kill-dead-eliminates-defined-features (D ↣ true  ∷ defined) D (here (is-refl D true )) l)
  (kill-dead-eliminates-defined-features (D ↣ false ∷ defined) D (here (is-refl D false)) r)

{-
Dead branch elimination of 2ADTs.
-}
kill-dead : ∀ {A}
  → 2ADT A
  → Undead2ADT A
kill-dead e = kill-dead-below [] e ⊚ kill-dead-correct [] e

{-
This translates a 2ADT to a VariantList.
This is correct only if the 2ADT is undead.
Otherwise, also dead variants will be part of
the resulting list.
-}
tr : ∀ {A : 𝔸} → 2ADT A → VariantList A
tr (leaf v) = v ∷ []
tr (D ⟨ l , r ⟩) = tr l ⁺++⁺ tr r

toVariantList : ∀ {A : 𝔸} → 2ADT A → VariantList A
toVariantList = tr ∘ node ∘ kill-dead

{-
This module proves that dead branch elimination preserves semantics.
-}
module DeadBranchElim where
  kill-dead-preserves-below-partial-configs : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → (defined : Path)
    → (c : Conf₂)
    → defined ⊑ c
    → ⟦ e ⟧₂ c ≡ ⟦ kill-dead-below defined e ⟧₂ c
  kill-dead-preserves-below-partial-configs (leaf _) _ _ _ = refl
  kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c with D ∈? def
  kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c | yes D∈def
    rewrite lookup-partial def⊑c D∈def
    with c D
  ... | true  = kill-dead-preserves-below-partial-configs l def c def⊑c
  ... | false = kill-dead-preserves-below-partial-configs r def c def⊑c
  kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c | no D∉def
    with c D in eq
  ... | true  = kill-dead-preserves-below-partial-configs l ((D ↣  true) ∷ def) c (eq ∷ def⊑c)
  ... | false = kill-dead-preserves-below-partial-configs r ((D ↣ false) ∷ def) c (eq ∷ def⊑c)

  -- Killing dead branches is ok.
  kill-dead-preserves : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → ⟦ e ⟧₂ ≅ ⟦ kill-dead e ⟧ᵤ
  kill-dead-preserves e = ≐→≅ (λ c → kill-dead-preserves-below-partial-configs e [] c [])

{-
This module proves that 'tr' preserves walk-semantics.
This means that when we evaluate 2ADTs by just walking "randomly"
down them, then simply converting a 2ADT to a variant list by
gathering all variants in leafs from left to right preserves semantics.
-}
module WalkToList where
  -- Converts a path to in the input 2ADT to the index in the resulting list.
  conff : ∀ {A} → (e : 2ADT A) → PathConfig e → ℕ
  conff .(leaf _) (.[] is-valid tleaf) = 0
  conff (D ⟨ l , _ ⟩) ((_ ∷ pl) is-valid walk-left  t) = conff l (pl is-valid t)
  conff (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) = length (tr l) + conff r (pr is-valid t)

  -- Converts an index from the resulting list back to a path in the input 2ADT.
  ffnoc : ∀ {A} → (e : 2ADT A) → ℕ → PathConfig e
  ffnoc (leaf v) _ = [] is-valid tleaf
  ffnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
  ffnoc (D ⟨ l , r ⟩) i | no _ {-left-} with ffnoc l i
  ... | pl is-valid tl = ((D ↣ true) ∷ pl) is-valid walk-left tl
  ffnoc (D ⟨ l , r ⟩) i | yes _  {-right-} with ffnoc r (i ∸ (length (tr l)))
  ... | pr is-valid tr = ((D ↣ false) ∷ pr) is-valid walk-right tr

  -- The index of a path will never be out of bounds.
  conff-bounded : ∀ {A}
    → (e : 2ADT A)
    → (c : PathConfig e)
    → conff e c < length (tr e)
  conff-bounded (leaf v) (.[] is-valid tleaf) = s≤s z≤n
  conff-bounded (D ⟨ l , r ⟩) ((.D ↣ true  ∷ p) is-valid walk-left  t) = ≤-trans (conff-bounded l (p is-valid t)) (⁺++⁺-length-≤ (tr l) (tr r))
  conff-bounded (D ⟨ l , r ⟩) ((.D ↣ false ∷ p) is-valid walk-right t) = go
    where
      c = p is-valid t

      -- get this by induction
      rb : conff r c < length (tr r)
      rb = conff-bounded r c

      -- add (length (tr l)) to both sides on the left
      gox : length (tr l) + conff r c < length (tr l) + length (tr r)
      gox = <-cong-+ˡ (length (tr l)) rb

      -- use the sum rule for ⁺++⁺ on the right hand side
      go : length (tr l) + conff r c < length (tr l ⁺++⁺ tr r)
      go rewrite ⁺++⁺-length (tr l) (tr r) = gox

  preservation-walk-to-list-conf : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → walk e ⊆[ conff e ] ⟦ tr e ⟧ₗ
  preservation-walk-to-list-conf .(leaf _) (.[] is-valid tleaf) = refl
  preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pl) is-valid walk-left t) =
    let c = pl is-valid t
    in
    begin
      walk l c
    ≡⟨ preservation-walk-to-list-conf l c ⟩
      ⟦ tr l ⟧ₗ (conff l c)
    ≡˘⟨ append-preserves (tr l) (tr r) (conff-bounded l c) ⟩
      ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conff l c)
    ∎
  preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) =
    let c = pr is-valid t
    in
    begin
      walk r c
    ≡⟨ preservation-walk-to-list-conf r c ⟩
      ⟦ tr r ⟧ₗ (conff r c)
    ≡˘⟨ prepend-preserves-+ (conff r c) (tr l) (tr r) ⟩
      ⟦ tr l ⁺++⁺ tr r ⟧ₗ (length (tr l) + (conff r c))
    ∎

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
      walk l (path (ffnoc l i) is-valid valid (ffnoc l i))
    ∎
  ... | yes len[tr-l]≤i  =
    begin
      ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
    ≡⟨⟩
      find-or-last i ((tr l) ⁺++⁺ (tr r))
    ≡⟨ prepend-preserves-∸ (tr l) (tr r) len[tr-l]≤i ⟩
      find-or-last (i ∸ length (tr l)) (tr r)
    ≡⟨⟩
      ⟦ tr r ⟧ₗ (i ∸ length (tr l))
    ≡⟨ preservation-walk-to-list-fnoc r (i ∸ length (tr l)) ⟩
      walk r (path (ffnoc r (i ∸ length (tr l))) is-valid valid (ffnoc r (i ∸ length (tr l))))
    ∎

  preservation-walk-to-list : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → walk e ≅ ⟦ tr e ⟧ₗ
  preservation-walk-to-list e = ≅[]→≅ (preservation-walk-to-list-conf e , preservation-walk-to-list-fnoc e)

{-
Walk semantics are equivalent to ordinary 2ADT semantics
as long as the 2ADT does not contain any dead branches.
This means that configurations can be modelled as functions or as paths.
Interestingly, we obtain a compiler that does not change the input
expression but only translates configurations.
-}
module NoConflictWalk where
  {-
  Converts a configuration function to a valid path within
  the given tree.
  The conversion checks the configuration function at each choice,
  constructs the path accordingly, and recurses until it reaches a leaf.
  -}
  fun-to-path : ∀ {A} (e : 2ADT A) → Conf₂ → PathConfig e
  fun-to-path (leaf _) _ = [] is-valid tleaf
  fun-to-path (D ⟨ _ , _ ⟩) c with c D
  fun-to-path (D ⟨ l , _ ⟩) c | true  with fun-to-path l c
  ... | pl is-valid tl = ((D ↣ true)  ∷ pl) is-valid walk-left tl
  fun-to-path (D ⟨ _ , r ⟩) c | false with fun-to-path r c
  ... | pr is-valid tr = ((D ↣ false) ∷ pr) is-valid walk-right tr

  {-
  Converts a path for the given tree to a function.
  When the returned function is queried for the value of a feature D',
  the function walks the path until it finds the respective feature in the
  tree and returns the value specified in the path.
  Otherwise, returns true.
  (The returned function returns true for all features that
  are not on a valid path.)
  -}
  path-to-fun : ∀ {A} (e : 2ADT A) → PathConfig e → Conf₂
  path-to-fun .(leaf _) ([] is-valid tleaf) _ = true
  path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .true) ∷ p) is-valid walk-left t) D' =
    if (isYes (D == D'))
    then true
    else path-to-fun l (p is-valid t) D'
  path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .false) ∷ p) is-valid walk-right t) D' =
    if (isYes (D == D'))
    then false
    else path-to-fun r (p is-valid t) D'

  {-
  When a given feature is not contained within a path,
  then the path cannot end in a sub-path containing that feature.
  TODO: There is probably a nicer, more general lemma hidden here.
  -}
  lem-not-endswith' : ∀ {D} {others q : Path}
    → (b : Bool)
    → All (different (D ↣ b)) others
    → ¬ (others endswith (D ↣ b ∷ q))
  lem-not-endswith' b (px ∷ all) (match .((_ ↣ b) ∷ _)) = toWitnessFalse px refl
  lem-not-endswith' b (px ∷ all) (later ends) = lem-not-endswith' b all ends

  -- more complex version of lem-not-endswith'
  lem-not-endswith : ∀ {D} {others q : Path}
    → (b : Bool)
    → All (different (D ↣ b)) others
    → ¬ (((D ↣ b) ∷ others) endswith ((D ↣ not b) ∷ q))
  lem-not-endswith false all (later ends) = lem-not-endswith' true all ends
  lem-not-endswith true all (later ends) = lem-not-endswith' false all ends

  {-
  Crucial lemma for proving preservation.
  path-to-fun returns the value b for a given feature D
  if the path given to path-to-fun contains the selection D ↣ b somewhere.
  -}
  path-to-fun-lem : ∀ {A} (D : F) (e : 2ADT A) (p q : Path) (t : p starts-at e)
    → (b : Bool)
    → Unique p
    → p endswith ((D ↣ b) ∷ q)
    → path-to-fun e (p is-valid t) D ≡ b
  path-to-fun-lem D (D' ⟨ _ , _ ⟩) (.D' ↣ true ∷ _) _ (walk-left  _) _ _ _ with D' == D
  path-to-fun-lem _ _ _ _ _ false (u ∷ _) x | yes refl = ⊥-elim (lem-not-endswith true u x)
  path-to-fun-lem _ _ _ _ _ true  _ _ | yes refl = refl
  path-to-fun-lem D (_ ⟨ l , _ ⟩) (_ ∷ others) q (walk-left  t) b (_ ∷ u-o) x | no  D≠D' = path-to-fun-lem D l others q t b u-o (endswith-tail (λ where refl → D≠D' refl) x)
  path-to-fun-lem D (D' ⟨ _ , _ ⟩) (D' ↣ false ∷ _) q (walk-right t) b _ x with D' == D
  path-to-fun-lem _ _ _ _ _ false _ _ | yes refl = refl
  path-to-fun-lem _ _ _ _ _ true  (u ∷ _) x | yes refl = ⊥-elim (lem-not-endswith false u x)
  path-to-fun-lem D (_ ⟨ _ , r ⟩) (_ ∷ others) q (walk-right  t) b (_ ∷ u-o) x | no  D≠D' = path-to-fun-lem D r others q t b u-o (endswith-tail (λ where refl → D≠D' refl) x)

  {-
  If a path p ends in a sub-path with a certain selection,
  that selection is within p, too.
  -}
  endswith-path-contains : ∀ {p q : Path} {D}
    → (b : Bool)
    → p endswith ((D ↣ b) ∷ q)
    → D ∈ p
  endswith-path-contains _ (match .((_ ↣ _) ∷ _)) = here (fromWitness refl)
  endswith-path-contains b (later x) = there (endswith-path-contains b x)

  path-to-fun-step-l-inner2 : ∀ {A}
    → (D : F) (l r : 2ADT A)
    → (p : Path) → (t : p starts-at l)
    → All (different (D ↣ true)) p
      -------------------------------------------------------------------
    → (E : F) → (E ∈ p)
    →   path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t) E
      ≡ path-to-fun l (p is-valid t) E
  path-to-fun-step-l-inner2 D l r p t all-dims-in-p-different-to-D E E∈p with D == E
  ... | yes refl = ⊥-elim (All-different→∉ true p all-dims-in-p-different-to-D E∈p)
  ... | no _ = refl

  -- clone-and-own from path-to-fun-step-l-inner2
  path-to-fun-step-r-inner2 : ∀ {A}
    → (D : F) (l r : 2ADT A)
    → (p : Path) → (t : p starts-at r)
    → All (different (D ↣ false)) p
      -------------------------------------------------------------------
    → (E : F) → (E ∈ p)
    →   path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ p) is-valid walk-right t) E
      ≡ path-to-fun r (p is-valid t) E
  path-to-fun-step-r-inner2 D l r p t all-dims-in-p-different-to-D E E∈p with D == E
  ... | yes refl = ⊥-elim (All-different→∉ true p all-dims-in-p-different-to-D E∈p)
  ... | no _ = refl

  path-to-fun-step-l-inner : ∀ {A}
    -- for a choice D ⟨ l , r ⟩
    → (D : F) (l r : 2ADT A)
    → (lp : Path)
    -- if there is a subexpression e
    → (e : 2ADT A) (ep : Path)
    -- (i.e., all paths starting in l end in paths starting in e)
    → (tlp : lp starts-at l)
    → (tep : ep starts-at e)
    → (sub : lp endswith ep)
    -- and if the left branch l is undead
    → All (different (D ↣ true)) lp -- this also means All (different (D ↣ true)) ep
    → Unique lp
    -- then it does not matter whether we convert the whole path from the choice to
    -- a function, or if we start at the left alternative below.
    →   ⟦ e ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ lp) is-valid walk-left tlp))
      ≡ ⟦ e ⟧₂ (path-to-fun l (lp is-valid tlp))
  path-to-fun-step-l-inner D l r lp (leaf v) ep tlp tep sub x _ = refl
  path-to-fun-step-l-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ .true) ∷ ep) tlp (walk-left tep) sub x u =
    begin
      ⟦ D' ⟨ a , b ⟩ ⟧₂ c-big
    ≡⟨⟩
      (if c-big D' then ⟦ a ⟧₂ c-big else ⟦ b ⟧₂ c-big)
    ≡⟨ Eq.cong (if_then ⟦ a ⟧₂ c-big else ⟦ b ⟧₂ c-big) (path-to-fun-step-l-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))) ⟩
      (if c-sml D' then ⟦ a ⟧₂ c-big else ⟦ b ⟧₂ c-big)
    ≡⟨ lem ⟩
      (if c-sml D' then ⟦ a ⟧₂ c-sml else ⟦ b ⟧₂ c-sml)
    ≡⟨⟩
      ⟦ D' ⟨ a , b ⟩ ⟧₂ c-sml
    ∎
    where
      c-big = λ D'' → if isYes (D == D'') then true else path-to-fun l (lp is-valid tlp) D''
      c-sml = path-to-fun l (lp is-valid tlp)

      force : c-sml D' ≡ true
      force = path-to-fun-lem D' l lp ep tlp true u sub

      lem : (if c-sml D' then ⟦ a ⟧₂ c-big else ⟦ b ⟧₂ c-big) ≡ (if c-sml D' then ⟦ a ⟧₂ c-sml else ⟦ b ⟧₂ c-sml)
      lem rewrite force = path-to-fun-step-l-inner D l r lp a ep tlp tep (endswith-shrink-suffix sub) x u
  path-to-fun-step-l-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ false) ∷ ep) tlp (walk-right tep) sub x u
    -- These rewrites are copied from the case above.
    rewrite path-to-fun-step-l-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
    rewrite path-to-fun-lem D' l lp ep tlp false u sub
    rewrite path-to-fun-step-l-inner D l r lp b ep tlp tep (endswith-shrink-suffix sub) x u
    = refl

  -- This is a huge copy and paste blob from
  -- path-to-fun-step-r-inner
  path-to-fun-step-r-inner : ∀ {A}
    → (D : F) (l r : 2ADT A)
    → (rp : Path)
    → (e : 2ADT A) (ep : Path)
    → (trp : rp starts-at r)
    → (tep : ep starts-at e)
    → (sub : rp endswith ep)
    → All (different (D ↣ false)) rp
    → Unique rp
    →   ⟦ e ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ rp) is-valid walk-right trp))
      ≡ ⟦ e ⟧₂ (path-to-fun r (rp is-valid trp))
  path-to-fun-step-r-inner D l r lp (leaf v) ep tlp tep sub x _ = refl
  path-to-fun-step-r-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ .true) ∷ ep) tlp (walk-left tep) sub x u
    rewrite path-to-fun-step-r-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
    rewrite path-to-fun-lem D' r lp ep tlp true u sub
    rewrite path-to-fun-step-r-inner D l r lp a ep tlp tep (endswith-shrink-suffix sub) x u
    = refl
  path-to-fun-step-r-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ false) ∷ ep) tlp (walk-right tep) sub x u
    -- These rewrites are copied from the case above.
    rewrite path-to-fun-step-r-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
    rewrite path-to-fun-lem D' r lp ep tlp false u sub
    rewrite path-to-fun-step-r-inner D l r lp b ep tlp tep (endswith-shrink-suffix sub) x u
    = refl

  path-to-fun-step-l : ∀ {A}
    → (D : F) (l r : 2ADT A)
    → Undead (D ⟨ l , r ⟩)
    → (p : Path)
    → (t : p starts-at l)
    →   ⟦ l ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t))
      ≡ ⟦ l ⟧₂ (path-to-fun l (p is-valid t))
  path-to-fun-step-l D l r u p t with u ((D ↣ true) ∷ p) (walk-left t)
  ... | u ∷ uu = path-to-fun-step-l-inner D l r p l p t t (match p) u uu

  path-to-fun-step-r : ∀ {A}
    → (D : F) (l r : 2ADT A)
    → Undead (D ⟨ l , r ⟩)
    → (p : Path)
    → (t : p starts-at r)
    →   ⟦ r ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ p) is-valid walk-right t))
      ≡ ⟦ r ⟧₂ (path-to-fun r (p is-valid t))
  path-to-fun-step-r D l r u p t with u ((D ↣ false) ∷ p) (walk-right t)
  ... | u ∷ uu = path-to-fun-step-r-inner D l r p r p t t (match p) u uu

  path-to-fun-head : ∀ {A}
    → (D : F)
    → (l r : 2ADT A)
    → (b : Bool)
    → (p : Path)
    → (t : ((D ↣ b) ∷ p) starts-at (D ⟨ l , r ⟩))
    → path-to-fun (D ⟨ l , r ⟩) (((D ↣ b) ∷ p) is-valid t) D ≡ b
  path-to-fun-head D l r .true p (walk-left t) with D == D
  ... | yes D≡D = refl
  ... | no  D≢D = ⊥-elim (D≢D refl)
  path-to-fun-head D l r .false p (walk-right t) with D == D
  ... | yes D≡D = refl
  ... | no  D≢D = ⊥-elim (D≢D refl)

  preservation-path-configs-conf : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → (u : Undead e)
    → ⟦ e ⊚ u ⟧ᵤ ⊆[ fun-to-path e ] walk e
  preservation-path-configs-conf (leaf _) _ _ = refl
  preservation-path-configs-conf (D ⟨ _ , _ ⟩) _ c with c D
  preservation-path-configs-conf (_ ⟨ l , _ ⟩) u c | true  with fun-to-path l c in eq
  ... | pl is-valid tl =
    begin
      ⟦ l ⟧₂ c
    ≡⟨⟩
      ⟦ l ⊚ undead-left u ⟧ᵤ c
    ≡⟨ preservation-path-configs-conf l (undead-left u) c ⟩
      walk l (fun-to-path l c)
    ≡⟨ Eq.cong (walk l) eq ⟩
      walk l (pl is-valid tl)
    ∎
  preservation-path-configs-conf (_ ⟨ _ , r ⟩) u c | false with fun-to-path r c in eq
  ... | _ rewrite (sym eq) = preservation-path-configs-conf r (undead-right u) c

  preservation-path-configs-fnoc : ∀ {A : 𝔸}
    → (e : 2ADT A)
    → (u : Undead e)
    → walk e ⊆[ path-to-fun e ] ⟦ e ⊚ u ⟧ᵤ
  preservation-path-configs-fnoc (leaf v) _ (.[] is-valid tleaf) = refl
  preservation-path-configs-fnoc (D ⟨ l , r ⟩) u c@((.(D ↣ true ) ∷ p) is-valid walk-left t)
    rewrite path-to-fun-head D l r true p (walk-left t) =
    begin
      walk l (p is-valid t)
    ≡⟨ preservation-path-configs-fnoc l (undead-left u) (p is-valid t) ⟩
      ⟦ l ⟧₂ (path-to-fun l (p is-valid t))
    ≡˘⟨ path-to-fun-step-l D l r u p t ⟩
      ⟦ l ⟧₂ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t))
    ≡⟨⟩
      ⟦ l ⟧₂ (λ D' → if isYes (D == D') then true else path-to-fun l (p is-valid t) D')
    ∎
  preservation-path-configs-fnoc (D ⟨ l , r ⟩) u ((.(D ↣ false) ∷ p) is-valid walk-right t)
    rewrite path-to-fun-head D l r false p (walk-right t)
    rewrite preservation-path-configs-fnoc r (undead-right u) (p is-valid t)
    rewrite path-to-fun-step-r D l r u p t
    = refl

  preservation-path-configs : ∀ {A : 𝔸}
    → (e : Undead2ADT A)
    → ⟦ e ⟧ᵤ ≅ walk (node e)
  preservation-path-configs e = ≅[]→≅ (preservation-path-configs-conf (node e) (undead e) , preservation-path-configs-fnoc (node e) (undead e))

-- 2ADTs are isomorphic to Variant Lists.
-- TODO: Construct compilers and make use of ⊕.
preservation : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ e ⟧₂ ≅ ⟦ toVariantList e ⟧ₗ
preservation e =
  ≅-begin
    ⟦ e ⟧₂
  ≅⟨ DeadBranchElim.kill-dead-preserves e ⟩ -- todo
    ⟦ kill-dead e ⟧ᵤ
  ≅⟨ NoConflictWalk.preservation-path-configs (kill-dead e) ⟩ -- done
    walk (node (kill-dead e))
  ≅⟨ WalkToList.preservation-walk-to-list (node (kill-dead e)) ⟩ -- conceptually done
    ⟦ toVariantList e ⟧ₗ
  ≅-∎

VariantList≽2ADT : VariantListL ≽ 2ADTL
VariantList≽2ADT = expressiveness-by-translation toVariantList preservation
