{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Lang.FST (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; foldr; map; filterᵇ; concat; reverse)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Size using (∞)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Annotation.Name using (Name)
open import Framework.Variants using (Rose; rose)
open import Framework.Composition.FeatureAlgebra
open import Construct.Artifact as At using ()

Conf : Set
Conf = F → Bool

module TODO-MOVE-TO-AUX-OR-USE-STL where
  lem : ∀ {ℓ} {A : Set ℓ} (y : A) (ys xs : List A)
    → (xs ++ y ∷ []) ++ ys ≡ (xs ++ (y ∷ ys))
  lem y ys [] = refl
  lem y ys (x ∷ xs) = Eq.cong (x ∷_) (lem y ys xs)
open TODO-MOVE-TO-AUX-OR-USE-STL

FST : 𝔼
FST = Rose ∞

pattern _-<_>- a cs = rose (a At.-< cs >-)

induction : ∀ {A : 𝔸} {B : Set} → (A → List B → B) → FST A → B
induction {A} {B} f n = go n [] where
  go : FST A → List B → B
  go (a -< [] >-) bs = f a (reverse bs)
  go (a -< c ∷ cs >-) bs = go (a -< cs >-) (go c [] ∷ bs)

infix 15 _≈_
_≈_ : ∀ {A} → Rel (FST A) 0ℓ
(a -< _ >-) ≈ (b -< _ >-) = a ≡ b

≈-sym : ∀ {A} → (a b : FST A) → a ≈ b → b ≈ a
≈-sym (a -< _ >-) (.a -< _ >-) refl = refl

infix 15 _≉_
_≉_ : ∀ {A} → Rel (FST A) 0ℓ
a ≉ b = ¬ (a ≈ b)

≉-sym : ∀ {A} → (a b : FST A) → a ≉ b → b ≉ a
≉-sym a b a≉b b≈a = a≉b (≈-sym b a b≈a)

infix 15 _∈_
_∈_ : ∀ {A} → FST A → List (FST A) → Set
x ∈ xs = Any (x ≈_) xs

infix 15 _∉_
_∉_ : ∀ {A} → FST A → List (FST A) → Set
x ∉ xs = All (x ≉_) xs

_⊑_ : ∀ {A} → (xs ys : List (FST A)) → Set --\squb=
xs ⊑ ys = All (_∈ ys) xs

_⋢_ : ∀ {A} → (xs ys : List (FST A)) → Set --\squb=n
xs ⋢ ys = Any (_∉ ys) xs

Disjoint : ∀ {A} → (xs ys : List (FST A)) → Set --\squb=n
Disjoint xs ys = All (_∉ ys) xs

-- identity of proofs
open import Axioms.Extensionality using (extensionality)
≉-deterministic : ∀ {A} (x y : FST A)
  → (p₁ : x ≉ y)
  → (p₂ : x ≉ y)
  → p₁ ≡ p₂
≉-deterministic (a -< _ >-) (b -< _ >-) p₁ p₂ = extensionality λ where refl → refl

∉-deterministic : ∀ {A} {x : FST A} (ys : List (FST A))
  → (p₁ : x ∉ ys)
  → (p₂ : x ∉ ys)
  → p₁ ≡ p₂
∉-deterministic [] [] [] = refl
∉-deterministic {_} {x} (y ∷ ys) (x≉y₁ ∷ pa) (x≉y₂ ∷ pb)
  rewrite ≉-deterministic x y x≉y₁ x≉y₂
  rewrite ∉-deterministic ys pa pb
  = refl

map-≉ : ∀ {A} {b xs} (ys : List (FST A)) (z : FST A)
  → b -< xs >- ≉ z
  → b -< ys >- ≉ z
map-≉ ys (z -< zs >-) z≉z refl = z≉z refl

map-∉ : ∀ {A} {b : A} {cs cs' xs : List (FST A)}
  → b -< cs  >- ∉ xs
  → b -< cs' >- ∉ xs
map-∉ [] = []
map-∉ {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-≉ cs' x px ∷ map-∉ pxs

disjoint-[]ˡ : ∀ {A} (xs : List (FST A)) → Disjoint [] xs
disjoint-[]ˡ _ = []

disjoint-[]ʳ : ∀ {A} (xs : List (FST A)) → Disjoint xs []
disjoint-[]ʳ [] = []
disjoint-[]ʳ (x ∷ xs) = [] ∷ (disjoint-[]ʳ xs)

disjoint-grow : ∀ {A} (r : FST A) (rs ls : List (FST A))
  → Disjoint ls rs
  → r ∉ ls
  → Disjoint ls (r ∷ rs)
disjoint-grow r rs [] _ _ = []
disjoint-grow r rs (l ∷ ls) (l∉rs ∷ d-ls-rs) (r≉l ∷ r∉ls)
  = (≉-sym r l r≉l ∷ l∉rs) ∷ disjoint-grow r rs ls d-ls-rs r∉ls

disjoint-shiftʳ : ∀ {A} (r : FST A) (rs ls : List (FST A))
  → Disjoint ls (r ∷ rs)
  → Disjoint ls (rs ++ r ∷ [])
disjoint-shiftʳ r rs [] x = []
disjoint-shiftʳ r rs (l ∷ ls) ((l≉r ∷ l∉rs) ∷ d-ls-rrs)
  = step l r rs l≉r l∉rs ∷ disjoint-shiftʳ r rs ls d-ls-rrs
  where
    step : ∀ {A} (x y : FST A) (zs : List (FST A))
      → x ≉ y
      → x ∉ zs
      → x ∉ (zs ++ y ∷ [])
    step x y [] x≉y _ = x≉y ∷ []
    step x y (z ∷ zs) x≉y (x≉z ∷ x∉zs) = x≉z ∷ step x y zs x≉y x∉zs

-- the syntax used in the paper for paths
infixr 5 _．_
_．_ : ∀ {A} → A → (cs : List (FST A)) → List (FST A)
a ． cs = a -< cs >- ∷ []

-- helper function when branching in paths
branches : ∀ {A} → List (List (FST A)) → List (FST A)
branches = concat

mutual
  infix 4 _⊙_↝_
  data _⊙_↝_ : ∀ {A} → FST A → List (FST A) → List (FST A) → Set where
    base : ∀ {A} {l : FST A}
        ---------------
      → l ⊙ [] ↝ l ∷ []

    merge : ∀ {A} {a : A} {as bs rs cs : List (FST A)}
      → as + bs ↪ cs
        ----------------------------------------------
      → a -< as >- ⊙ a -< bs >- ∷ rs ↝ a -< cs >- ∷ rs

    -- In the original work, skipped nodes were added to the left.
    -- We add to the right here because it fits nicer with list construction _∷_
    -- Otherwise, we would have to backtrack when we found no match in rs.
    skip : ∀ {A} {a r : FST A} {rs cs : List (FST A)}
      → a ≉ r
      → a ⊙ rs ↝ cs
        ----------------------------------------------
      → a ⊙ r ∷ rs ↝ r ∷ cs

  -- This is basically just a fold on lists. Maybe we can simplify it accordingly.
  infix 4 _+_↪_
  data _+_↪_ : ∀ {A} → List (FST A) → List (FST A) → List (FST A) → Set where
    impose-nothing : ∀ {A} {rs : List (FST A)}
      → [] + rs ↪ rs

    impose-step : ∀ {A} {l : FST A} {ls rs e e' : List (FST A)}
      → l  ⊙ rs ↝ e'
      → ls + e' ↪ e
        ----------------
      → l ∷ ls + rs ↪ e

mutual
  ↪-deterministic : ∀ {A} {fs rs e e' : List (FST A)}
    → fs + rs ↪ e
    → fs + rs ↪ e'
    → e ≡ e'
  ↪-deterministic impose-nothing impose-nothing = refl
  ↪-deterministic (impose-step ↝x ↪x) (impose-step ↝y ↪y) rewrite ↝-deterministic ↝x ↝y | ↪-deterministic ↪x ↪y = refl

  ↝-deterministic : ∀ {A} {f : FST A} {rs e e' : List (FST A)}
    → f ⊙ rs ↝ e
    → f ⊙ rs ↝ e'
    → e ≡ e'
  ↝-deterministic base base = refl
  ↝-deterministic (merge x) (merge y) rewrite ↪-deterministic x y = refl
  ↝-deterministic (merge x) (skip a≠a y) = ⊥-elim (a≠a refl)
  ↝-deterministic (skip a≠a x) (merge y) = ⊥-elim (a≠a refl)
  ↝-deterministic (skip neq x) (skip neq' y) rewrite ↝-deterministic x y = refl

↪-return : ∀ {A} {e ls rs : List (FST A)}
  → ls + rs ↪ e
  → ∃[ e ] (ls + rs ↪ e)
↪-return {e = e} ↪e = e , ↪e

↝-return : ∀ {A} {l : FST A} {e rs : List (FST A)}
  → l ⊙ rs ↝ e
  → ∃[ e ] (l ⊙ rs ↝ e)
↝-return {e = e} ↝e = e , ↝e

module Impose {A : 𝔸} (_≟_ : DecidableEquality A) where
  _==_ : Decidable (_≈_ {A})
  (a -< _ >-) == (b -< _ >-) = a ≟ b

  childs : FST A → List (FST A)
  childs (a -< as >-) = as

  mutual
    ↪-total : ∀ (ls rs : List (FST A)) → ∃[ e ] (ls + rs ↪ e)
    ↪-total [] rs = ↪-return impose-nothing
    ↪-total (a -< as >- ∷ ls) rs =
      let e' , ↝e' = ↝-total (a -< as >-) rs (↪-total as)
          _  , ↪e  = ↪-total ls e'
      in ↪-return (impose-step ↝e' ↪e)

    ↝-total : ∀ (l : FST A) (rs : List (FST A))
      → ((rs' : List (FST A)) → ∃[ e ] (childs l + rs' ↪ e))
      → ∃[ e ] (l ⊙ rs ↝ e)
    ↝-total l [] _ = ↝-return base
    ↝-total (a -< as >-) (b -< bs >- ∷ rs) ↪-total-as with a ≟ b
    ... | yes refl =
      let cs , ↪cs = ↪-total-as bs
      in ↝-return (merge ↪cs)
    ... | no  a≠b =
      let cs , ↝cs = ↝-total (a -< as >-) rs ↪-total-as
      in ↝-return (skip a≠b ↝cs)

  Unique : List (FST A) → Set
  Unique = AllPairs _≉_

  unique-ignores-children : ∀ {a as bs rs}
    → Unique (a -< as >- ∷ rs)
    → Unique (a -< bs >- ∷ rs)
  unique-ignores-children (x ∷ xs) = map-∉ x ∷ xs

  drop-second-Unique : ∀ {x y zs}
    → Unique (x ∷ y ∷ zs)
    → Unique (x ∷ zs)
  drop-second-Unique ((_ ∷ pxs) ∷ _ ∷ zs) = pxs ∷ zs

  mutual
    data UniqueNode : FST A → Set where
      unq : ∀ {a cs} → UniqueR cs → UniqueNode (a -< cs >-)

    UniqueR : List (FST A) → Set
    UniqueR cs = Unique cs × All UniqueNode cs

  mutual
    UniqueNode-deterministic : ∀ {x : FST A}
      → (a : UniqueNode x)
      → (b : UniqueNode x)
      → a ≡ b
    UniqueNode-deterministic {_ -< cs >- } (unq a) (unq b) = Eq.cong unq (UniqueR-deterministic cs a b)

    UniqueR-deterministic : ∀ (xs : List (FST A))
      → (ua : UniqueR xs)
      → (ub : UniqueR xs)
      → ua ≡ ub
    UniqueR-deterministic [] ([] , []) ([] , []) = refl
    UniqueR-deterministic (x ∷ xs) (a-x∉xs ∷ a-u-xs , a-ur-x ∷ a-ur-xs) (b-x∉xs ∷ b-u-xs , b-ur-x ∷ b-ur-xs)
      with UniqueR-deterministic xs (a-u-xs , a-ur-xs) (b-u-xs , b-ur-xs)
    ... | eq
      rewrite (Eq.cong proj₁ eq)
      rewrite (Eq.cong proj₂ eq)
      rewrite UniqueNode-deterministic a-ur-x b-ur-x
      rewrite ∉-deterministic xs a-x∉xs b-x∉xs
      = refl

  mutual
    ↪-preserves-unique : ∀ {ls rs e : List (FST A)}
      → ls + rs ↪ e
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ↪-preserves-unique impose-nothing ur-ls ur-rs = ur-rs
    ↪-preserves-unique {a -< as >- ∷ ls} {rs} (impose-step {e' = e'} ↝e' ↪e) (u-l ∷ u-ls , unq ur-as ∷ ur-ls) ur-rs =
      let ur-e' = ↝-preserves-unique a as rs e' ↝e' ur-as ur-rs
          ur-e  = ↪-preserves-unique ↪e (u-ls , ur-ls) ur-e'
       in ur-e

    ↝-preserves-unique : ∀ (a : A) (ls rs : List (FST A)) (e : List (FST A))
      → a -< ls >- ⊙ rs ↝ e
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ↝-preserves-unique _ _ _ _ base ur-ls _ = [] ∷ [] , (unq ur-ls) ∷ []
    ↝-preserves-unique a ls (.a -< bs >- ∷ rs) e@(.a -< cs >- ∷ rs) (merge ↪e) ur-ls (u-rs , (unq ur-bs) ∷ un-rs)
      = unique-ignores-children u-rs , unq (↪-preserves-unique ↪e ur-ls ur-bs) ∷ un-rs
    ↝-preserves-unique a ls (b -< bs >- ∷ rs) (.b -< .bs >- ∷ cs) (skip a≠b ↝cs) u-ls (u-r ∷ u-rs , ur-bs ∷ ur-rs)
      = ind a≠b (u-r ∷ u-rs) ↝cs ∷ u-cs , ur-bs ∷ un-cs
      where
        ur-cs = ↝-preserves-unique a ls rs cs ↝cs u-ls (u-rs , ur-rs)
        u-cs = proj₁ ur-cs
        un-cs = proj₂ ur-cs

        ind : ∀ {a ls b bs cs rs}
          → ¬ (a ≡ b)
          → Unique (b -< bs >- ∷ rs)
          → a -< ls >- ⊙ rs ↝ cs
          → All (_≉_ (b -< bs >-)) cs
        ind {a} {ls} {b} {bs} a≠b _ base = ≉-sym (a -< ls >-) (b -< bs >-) a≠b ∷ []
        ind {a} {_} {b} {bs} {.a -< cs >- ∷ _} a≠b u-rs (merge _) = ≉-sym (a -< cs >-) (b -< bs >-) a≠b ∷ head (drop-second-Unique u-rs)
        ind a≠b ((b≠b' ∷ u-r) ∷ _ ∷ u-rs) (skip a≠b' ↝cs) = b≠b' ∷ ind a≠b (u-r ∷ u-rs) ↝cs

  -- Feature Structure Forest
  record FSF : Set where
    constructor _⊚_
    field
      trees : List (FST A)
      valid : UniqueR trees
  open FSF public

  ↝-append-strange : ∀ (l : FST A) (rs : List (FST A))
    → l ∉ rs
    → l ⊙ rs ↝ rs ∷ʳ l
  ↝-append-strange l [] _ = base
  ↝-append-strange l (r ∷ rs) (l≠r ∷ l∉rs) = skip l≠r (↝-append-strange l rs l∉rs)

  ↪-append-strangers : ∀ (ls rs : List (FST A))
    → Unique ls
    → Disjoint ls rs
    → ls + rs ↪ rs ++ ls
  ↪-append-strangers [] rs _ _ rewrite ++-identityʳ rs = impose-nothing
  ↪-append-strangers (l ∷ ls) rs (l∉ls ∷ u-ls) (l∉rs ∷ d-ls-rs)
    rewrite (Eq.sym (lem l ls rs))
    with ↝-append-strange l rs l∉rs
  ... | x
    = impose-step x (↪-append-strangers ls (rs ++ l ∷ []) u-ls
        (disjoint-shiftʳ l rs ls (disjoint-grow l rs ls d-ls-rs l∉ls)))

  impose-nothing-r :
    ∀ (ls : List (FST A))
    → Unique ls
    → ls + [] ↪ ls
  impose-nothing-r ls u-ls = ↪-append-strangers ls [] u-ls (disjoint-[]ʳ ls)

  forget-uniqueness : FSF → List (FST A)
  forget-uniqueness = trees

  {-
  A feature is a named feature structure tree.
  All features in a product line are required to have
  the very same root node, otherwise they could not be
  imposed.
  To ensure this constraint by design, this root node is
  part of the SPL definition and not the feature.
  Hence, a feature is a rootless tree: It holds a list of trees,
  which denote the children of the common root.
  -}
  infixr 3 _::_
  record Feature : Set where
    constructor _::_
    field
      name : Name F
      impl : FSF
  open Feature public

  record SPL : Set where
    constructor _◀_
    field
      root : A
      features : List Feature
  open SPL public

  select : Conf → List Feature → List FSF
  select _ [] = []
  select c (f ∷ fs) =
    if c (name f)
    then impl f ∷ select c fs
    else          select c fs

  names : SPL → List F
  names = map name ∘ features

  ---- Algebra ----
  open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)
  open Eq.≡-Reasoning

  𝟘 : FSF
  𝟘 = [] ⊚ ([] , [])

  infixr 7 _⊕_
  _⊕_ : FSF → FSF → FSF
  (l ⊚ u-l) ⊕ (r ⊚ u-r) =
    let e , ↪e = ↪-total l r
        u-e    = ↪-preserves-unique ↪e u-l u-r
     in e ⊚ u-e

  ⊕-all : List FSF → FSF
  ⊕-all = foldr _⊕_ 𝟘

  l-id : LeftIdentity _≡_ 𝟘 _⊕_
  l-id _ = refl

  r-id : RightIdentity _≡_ 𝟘 _⊕_
  r-id (xs ⊚ (u-xs , ur-xs))
    -- Let's see what ⊕ does
    with ↪-total xs []
    -- it computes some result 'e' and a derivation 'deriv'
  ... | (e , deriv)
    -- However, we know by impose-nothing-r that we can derive
    -- 'xs' itself as result.
    -- By determinism, we know that there can only be one derivation
    -- so e = xs.
    -- (We can't do a rewrite here for some reason so we stick to good old "with".)
    with ↪-deterministic deriv (impose-nothing-r xs u-xs)
  ... | refl = Eq.cong (xs ⊚_) (help xs (u-xs , ur-xs) deriv)
    where
      -- lastly, we have to prove that the typing is also unique but that is actually
      -- irrelevant. Maybe we can avoid this proof somehow?
      -- Its never needed and just an artifical problem.
      -- Maybe we shouldnt prove for _≡_ but rather for a new eq relation
      -- that is weaker and ignores the typing.
      help : ∀ (ls : List (FST A))
        → (ur-ls : UniqueR ls)
        → (deriv : ls + [] ↪ ls)
        → ↪-preserves-unique deriv ur-ls ([] , []) ≡ ur-ls
      help ls ur-ls deriv = UniqueR-deterministic ls (↪-preserves-unique deriv ur-ls ([] , [])) ur-ls

  assoc : Associative _≡_ _⊕_
  assoc x y z = {!!}

  cong : Congruent₂ _≡_ _⊕_
  cong refl refl = refl

  idem : ∀ (i₁ i₂ : FSF) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂
  idem = {!!}

  FST-is-FeatureAlgebra : FeatureAlgebra FSF _⊕_ 𝟘
  FST-is-FeatureAlgebra = record
    { monoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = cong
          }
        ; assoc = assoc
        }
      ; identity = l-id , r-id
      }
    ; distant-idempotence = idem
    }
    where
      open import Data.Product using (_,_)

  -- Semantics
  ⟦_⟧ : SPL → Conf → Rose ∞ A
  ⟦ r ◀ features ⟧ c = r -< forget-uniqueness (⊕-all (select c features)) >-

  open import Data.String using (String; _<+>_)
  open import Show.Lines

  module Show (show-F : F → String) (show-A : A → String) where
    mutual
      show-FST : FST A → Lines
      show-FST = induction λ a children → do
        > show-A a
        indent 2 (lines children)

      show-FSF : List (FST A) → Lines
      show-FSF roots = lines (map show-FST roots)

      show-Feature : Feature → Lines
      show-Feature feature = do
        > show-F (name feature) <+> "∷"
        indent 2 (show-FSF (forget-uniqueness (impl feature)))
