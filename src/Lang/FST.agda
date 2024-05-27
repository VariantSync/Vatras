{-# OPTIONS --allow-unsolved-metas #-}

open import Framework.Definitions

{-
This module formalizes feature structure trees.
We formalized the language, its semantics, and the typing to disallow duplicate neighbors.
We also prove that FSTs are a feature algebra but the proof is work in progress.
-}
module Lang.FST (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; foldl; foldr; map; filterᵇ; concat; reverse)
open import Data.List.Properties as List using (++-identityˡ; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃-syntax; ∄-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Size using (Size; ↑_; ∞)

open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Framework.Annotation.Name using (Name)
open import Framework.Variants using (Rose; _-<_>-; rose-leaf; children-equality)
open import Framework.Composition.FeatureAlgebra
open import Framework.VariabilityLanguage
open import Framework.VariantMap using (VMap)
import Construct.Artifact as At
open import Framework.Properties.Completeness using (Incomplete)

Conf : Set
Conf = F → Bool

module TODO-MOVE-TO-AUX-OR-USE-STL where
  lem : ∀ {ℓ} {A : Set ℓ} (y : A) (ys xs : List A)
    → (xs ++ y ∷ []) ++ ys ≡ (xs ++ (y ∷ ys))
  lem y ys [] = refl
  lem y ys (x ∷ xs) = Eq.cong (x ∷_) (lem y ys xs)
open TODO-MOVE-TO-AUX-OR-USE-STL

FST : Size → 𝔼
FST i = Rose i

fst-leaf = rose-leaf

induction : ∀ {A : 𝔸} {B : Set} → (atoms A → List B → B) → FST ∞ A → B
induction {A} {B} f n = go n [] where
  go : FST ∞ A → List B → B
  go (a -< [] >-) bs = f a (reverse bs)
  go (a -< c ∷ cs >-) bs = go (a -< cs >-) (go c [] ∷ bs)

infix 15 _≈_
_≈_ : ∀ {A i} → Rel (FST i A) 0ℓ
(a -< _ >-) ≈ (b -< _ >-) = a ≡ b

≈-refl : ∀ {A i} → {a : FST i A} → a ≈ a
≈-refl {A} {.(↑ _)} {_ -< _ >- } = refl

≈-reflexive : ∀ {A i} → {a b : FST i A} → a ≡ b → a ≈ b
≈-reflexive {A} {.(↑ _)} {_ -< _ >- } refl = refl

≈-sym : ∀ {A i} → {a b : FST i A} → a ≈ b → b ≈ a
≈-sym {A} {i} {(a -< _ >-)} {(.a -< _ >-)} refl = refl

≈-trans : ∀ {A i} → {a b c : FST i A} → a ≈ b → b ≈ c → a ≈ c
≈-trans {A} {i} {(a -< _ >-)} {(.a -< _ >-)} {(.a -< _ >-)} refl refl = refl

infix 15 _≉_
_≉_ : ∀ {A i} → Rel (FST i A) 0ℓ
a ≉ b = ¬ (a ≈ b)

≉-sym : ∀ {A i} → {a b : FST i A} → a ≉ b → b ≉ a
≉-sym a≉b b≈a = a≉b (≈-sym b≈a)

≉-ignores-children : ∀ {A i} → {a₁ a₂ b₁ b₂ : FST i A} → a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ≉ b₁ → a₂ ≉ b₂
≉-ignores-children a₁≈a₂ b₁≈b₂ a₁≉b₁ a₂≈b₂ = a₁≉b₁ (≈-trans a₁≈a₂ (≈-trans a₂≈b₂ (≈-sym b₁≈b₂)))

-- TODO use standard library
infix 15 _∈_
_∈_ : ∀ {i A} → FST i A → List (FST i A) → Set₁
x ∈ xs = Any (x ≈_) xs

infix 15 _∉_
_∉_ : ∀ {i A} → FST i A → List (FST i A) → Set₁
x ∉ xs = All (x ≉_) xs

_⊑_ : ∀ {i A} → (xs ys : List (FST i A)) → Set₁ --\squb=
xs ⊑ ys = All (_∈ ys) xs

_⋢_ : ∀ {i A} → (xs ys : List (FST i A)) → Set₁ --\squb=n
xs ⋢ ys = Any (_∉ ys) xs

Disjoint : ∀ {i A} → (xs ys : List (FST i A)) → Set₁ --\squb=n
Disjoint xs ys = All (_∉ ys) xs

-- identity of proofs
open import Axioms.Extensionality using (extensionality)
≉-deterministic : ∀ {A} (x y : FST ∞ A)
  → (p₁ : x ≉ y)
  → (p₂ : x ≉ y)
  → p₁ ≡ p₂
≉-deterministic (a -< _ >-) (b -< _ >-) p₁ p₂ = extensionality λ where refl → refl

∉-deterministic : ∀ {A} {x : FST ∞ A} (ys : List (FST ∞ A))
  → (p₁ : x ∉ ys)
  → (p₂ : x ∉ ys)
  → p₁ ≡ p₂
∉-deterministic [] [] [] = refl
∉-deterministic {_} {x} (y ∷ ys) (x≉y₁ ∷ pa) (x≉y₂ ∷ pb)
  rewrite ≉-deterministic x y x≉y₁ x≉y₂
  rewrite ∉-deterministic ys pa pb
  = refl

map-≉ : ∀ {i} {A} {b xs} (ys : List (FST i A)) (z : FST (↑ i) A)
  → b -< xs >- ≉ z
  → b -< ys >- ≉ z
map-≉ ys (z -< zs >-) z≉z refl = z≉z refl

map-∉ : ∀ {i} {A : 𝔸} {b : atoms A} {cs cs' : List (FST i A)} {xs : List (FST (↑ i) A)}
  → b -< cs  >- ∉ xs
  → b -< cs' >- ∉ xs
map-∉ [] = []
map-∉ {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-≉ cs' x px ∷ map-∉ pxs

disjoint-[]ˡ : ∀ {i A} (xs : List (FST i A)) → Disjoint [] xs
disjoint-[]ˡ _ = []

disjoint-[]ʳ : ∀ {i A} (xs : List (FST i A)) → Disjoint xs []
disjoint-[]ʳ [] = []
disjoint-[]ʳ (x ∷ xs) = [] ∷ (disjoint-[]ʳ xs)

disjoint-grow : ∀ {i A} (r : FST i A) (rs ls : List (FST i A))
  → Disjoint ls rs
  → r ∉ ls
  → Disjoint ls (r ∷ rs)
disjoint-grow r rs [] _ _ = []
disjoint-grow r rs (l ∷ ls) (l∉rs ∷ d-ls-rs) (r≉l ∷ r∉ls)
  = (≉-sym r≉l ∷ l∉rs) ∷ disjoint-grow r rs ls d-ls-rs r∉ls

disjoint-shiftʳ : ∀ {i A} (r : FST i A) (rs ls : List (FST i A))
  → Disjoint ls (r ∷ rs)
  → Disjoint ls (rs ++ r ∷ [])
disjoint-shiftʳ r rs [] x = []
disjoint-shiftʳ r rs (l ∷ ls) ((l≉r ∷ l∉rs) ∷ d-ls-rrs)
  = step l r rs l≉r l∉rs ∷ disjoint-shiftʳ r rs ls d-ls-rrs
  where
    step : ∀ {i A} (x y : FST i A) (zs : List (FST i A))
      → x ≉ y
      → x ∉ zs
      → x ∉ (zs ++ y ∷ [])
    step x y [] x≉y _ = x≉y ∷ []
    step x y (z ∷ zs) x≉y (x≉z ∷ x∉zs) = x≉z ∷ step x y zs x≉y x∉zs

-- the syntax used in the paper for paths
infixr 5 _．_
_．_ : ∀ {A : 𝔸} → atoms A → (cs : List (FST ∞ A)) → List (FST ∞ A)
a ． cs = a -< cs >- ∷ []

-- helper function when branching in paths
branches : ∀ {A} → List (List (FST ∞ A)) → List (FST ∞ A)
branches = concat

module Impose (AtomSet : 𝔸) where
  FSTA : Size → Set₁
  FSTA i = FST i AtomSet

  private
    A = atoms AtomSet
    _≟_ = proj₂ AtomSet

  _==_ : ∀ {i} → Decidable (_≈_ {AtomSet} {i})
  (a -< _ >-) == (b -< _ >-) = a ≟ b

  -- ≟-refl : ∀ (x : A) → x ≡ x
  -- ≟-refl = {!!}

  mutual
    infixr 5 _⊕_
    _⊕_ : ∀ {i} → List (FSTA i) → List (FSTA i) → List (FSTA i)
    l ⊕ r = foldl _⊙_ l r

    -- Implementation without `foldl` for the paper.
    -- TODO inconsistent with paper, change the paper
    _⊕'_ : ∀ {i} → List (FSTA i) → List (FSTA i) → List (FSTA i)
    l ⊕' [] = l
    l ⊕' (r ∷ rs) = (l ⊙ r) ⊕' rs

    ⊕≗⊕' : ∀ xs ys → xs ⊕ ys ≡ xs ⊕' ys
    ⊕≗⊕' xs [] = refl
    ⊕≗⊕' xs (y ∷ ys) =
        xs ⊕ (y ∷ ys)
      ≡⟨⟩
        (xs ⊙ y) ⊕ ys
      ≡⟨ ⊕≗⊕' (xs ⊙ y) ys ⟩
        (xs ⊙ y) ⊕' (ys)
      ≡⟨⟩
        xs ⊕' (y ∷ ys)
      ∎

    infixl 5 _⊙_
    _⊙_ : ∀ {i} → List (FSTA i) → FSTA i → List (FSTA i)
    [] ⊙ r = r ∷ []
    (h ∷ t) ⊙ r with r == h
    ... | no _ = h ∷ (t ⊙ r)
    (a -< ca >- ∷ t) ⊙ .a -< cb >- | yes refl = a -< ca ⊕ cb >- ∷ t

  Unique : ∀ {i} → List (FSTA i) → Set₁
  Unique = AllPairs _≉_

  mutual
    WellFormed : ∀ {i} → FSTA i → Set₁
    WellFormed (_ -< cs >-) = AllWellFormed cs

    AllWellFormed : ∀ {i} → List (FSTA i) → Set₁
    AllWellFormed cs = Unique cs × All WellFormed cs

  mutual
    ⊕-wf : ∀ {i} {ls rs : List (FSTA i)}
      → AllWellFormed ls
      → AllWellFormed rs
      → AllWellFormed (ls ⊕ rs)
    ⊕-wf ls-wf ([] , []) = ls-wf
    ⊕-wf ls-wf (_ ∷ u-rs , du-r ∷ du-rs) = ⊕-wf (⊙-wf ls-wf du-r) (u-rs , du-rs)

    ⊙-wf : ∀ {i} {l : List (FSTA i)} {r : FSTA i}
      → AllWellFormed l
      → WellFormed r
      → AllWellFormed (l ⊙ r)
    ⊙-wf ([] , []) du-r = [] ∷ [] , du-r ∷ []
    ⊙-wf {_} {h ∷ _} {r} (_ ∷ _ , _ ∷ _) _ with r == h
    ⊙-wf {_} {(a -< ca >-) ∷ t} {.a -< cb >- } (  _ ∷ _   , wf-ca ∷    _) wf-cb | yes refl with ⊕-wf wf-ca wf-cb
    ⊙-wf                                       (u-h ∷ u-t ,     _ ∷ du-t) _     | yes refl | wf-ca⊕cb
      = (map-∉ u-h) ∷ u-t , wf-ca⊕cb ∷ du-t
    ⊙-wf {_} {a -< ca >- ∷ t} {b -< cb >- } (u-h ∷ u-t , du-h ∷ du-t) du-r | no _ with ⊙-wf (u-t , du-t) du-r
    ⊙-wf {_} {a -< ca >- ∷ t} {b -< cb >- } (u-h ∷ u-t , du-h ∷ du-t) du-r | no a≢b | u-rec , du-rec
      = ind a≢b u-h ∷ u-rec , du-h ∷ du-rec
      where
        ind :  ∀ {i} {a b} {ca cb : List (FSTA i)} {t : List (FSTA (↑ i))}
          → ¬ (a ≡ b)
          → b -< cb >- ∉ t
          → b -< cb >- ∉ (t ⊙ (a -< ca >-))
        ind {t = []} a≢b b∉t = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ []
        ind {_} {a} {_} {ca} {_}  {t ∷ ts} a≢b b∉t with (a -< ca >-) == t
        ind {_} {a} {_} {ca} {cb} {(.a -< ct >-) ∷ ts} a≢b (  _ ∷ b∉ts) | yes refl = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ b∉ts
        ind {_} {a} {_} {ca} {cb} {( t -< ct >-) ∷ ts} a≢b (b≢t ∷ b∉ts) | no   a≢t = b≢t ∷ (ind a≢b b∉ts)

  mutual
    WellFormed-deterministic : ∀ {x : FSTA ∞}
      → (a : WellFormed x)
      → (b : WellFormed x)
      → a ≡ b
    WellFormed-deterministic {_ -< cs >- } a b = AllWellFormed-deterministic cs a b

    AllWellFormed-deterministic : ∀ (xs : List (FSTA ∞))
      → (ua : AllWellFormed xs)
      → (ub : AllWellFormed xs)
      → ua ≡ ub
    AllWellFormed-deterministic [] ([] , []) ([] , []) = refl
    AllWellFormed-deterministic (x ∷ xs) (a-x∉xs ∷ a-u-xs , a-ur-x ∷ a-ur-xs) (b-x∉xs ∷ b-u-xs , b-ur-x ∷ b-ur-xs)
      with AllWellFormed-deterministic xs (a-u-xs , a-ur-xs) (b-u-xs , b-ur-xs)
    ... | eq
      rewrite (Eq.cong proj₁ eq)
      rewrite (Eq.cong proj₂ eq)
      rewrite WellFormed-deterministic a-ur-x b-ur-x
      rewrite ∉-deterministic xs a-x∉xs b-x∉xs
      = refl

  ⊙-stranger : ∀ {i} (l : FSTA i) (rs : List (FSTA i))
    → l ∉ rs
    → rs ⊙ l ≡ rs ∷ʳ l
  ⊙-stranger l [] _ = refl
  ⊙-stranger l (r ∷ rs) (l≢r ∷ l∉rs) with l == r -- TODO: Is there an easier way to tell Agda that we already know l ≢ r?
  ... | yes l≡r = ⊥-elim (l≢r l≡r)
  ... | no  _   = Eq.cong (r ∷_) (⊙-stranger l rs l∉rs)

  ⊕-strangers : ∀ {i} (ls rs : List (FSTA i))
    → Unique rs
    → Disjoint rs ls
    → ls ⊕ rs ≡ ls ++ rs
  ⊕-strangers ls [] _ _ rewrite ++-identityʳ ls = refl
  ⊕-strangers ls (r ∷ rs) (r∉rs ∷ u-rs) (r∉ls ∷ d-ls-rs)
-- Goal: (ls ⊙ r) ⊕ rs ≡ ls ++ r ∷ rs
    rewrite (Eq.sym (lem r rs ls))
-- Goal: (ls ⊙ r) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    rewrite ⊙-stranger r ls r∉ls
-- Goal: (ls ++ r ∷ []) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    = ⊕-strangers (ls ++ r ∷ []) rs u-rs (disjoint-shiftʳ r ls rs (disjoint-grow r ls rs d-ls-rs r∉rs))

  ⊕-idˡ :
    ∀ {i} (rs : List (FSTA i))
    → Unique rs
    → [] ⊕ rs ≡ rs
  ⊕-idˡ rs u-rs = ⊕-strangers [] rs u-rs (disjoint-[]ʳ rs)

  -- A proof that all FSTs xs are already imposed into another list of FSTs ys.
  data _lies-in_ : ∀ {i} → List (FSTA i) → List (FSTA i) → Set₁ where
    lempty : ∀ {i} {xs : List (FSTA i)}
        -------------
      → [] lies-in xs

    lstep-here : ∀ {i} {a b : A} {as bs : List (FSTA i)} {xs ys : List (FSTA (↑ i))}
      → a ≡ b
      → as lies-in bs
      → xs lies-in ys
        ---..................----------------------
      → (a -< as >- ∷ xs) lies-in (b -< bs >- ∷ ys)

    lstep-there : ∀ {i} {x y : FSTA i} {xs ys : List (FSTA i)}
      → x ≉ y
      → (x ∷ xs) lies-in ys
        -------------------------
      → (x ∷ xs) lies-in (y ∷ ys)

  _slice-of_ : ∀ {i} → FSTA i → FSTA i → Set₁
  x slice-of y = (x ∷ []) lies-in (y ∷ [])

  _slice-within_ : ∀ {i} → FSTA i → List (FSTA i) → Set₁
  x slice-within ys = (x ∷ []) lies-in ys

  lies-in-refl : ∀ {i} → (xs : List (FSTA i)) → xs lies-in xs
  lies-in-refl [] = lempty
  lies-in-refl ((a -< as >-) ∷ xs) = lstep-here refl (lies-in-refl as) (lies-in-refl xs)

  slice-prop : ∀ {i} {xs ys : List (FSTA i)} (zs : List (FSTA i))
    → xs lies-in ys
    → xs lies-in (ys ⊕ zs)
  slice-prop zs lempty = lempty
  slice-prop {xs = a -< as >- ∷ xs} {ys = .a -< bs >- ∷ ys} zs (lstep-here refl as-lies-in-bs xs-lies-in-ys) = {!lstep-here!}
  slice-prop zs (lstep-there x x₁) = {!!}

  slice-concat : ∀ {i} {x : FSTA i} {ys : List (FSTA i)} (xs : List (FSTA i))
    → x slice-within ys
    → (x ∷ xs) lies-in (ys ⊕ xs)
  slice-concat = {!!}

  -- mutual
  --   ⊕-makes-slicesˡ : ∀ {i} (xs ys : List (FSTA i))
  --     → xs lies-in (ys ⊕ xs)
  --   ⊕-makes-slicesˡ [] ys = lempty
  --   ⊕-makes-slicesˡ (x ∷ xs) ys = slice-concat xs (⊙-makes-slice-head x ys)

  --   ⊕-makes-slicesʳ : ∀ {i} (xs ys : List (FSTA i))
  --     → xs lies-in (xs ⊕ ys)
  --   ⊕-makes-slicesʳ xs []       = lies-in-refl xs
  --   ⊕-makes-slicesʳ xs (y ∷ ys) = slice-prop ys (⊙-makes-slice-tail y xs)

  --   ⊙-makes-slice-tail : ∀ {i} (x : FSTA i) (ys : List (FSTA i))
  --     → ys lies-in (x ⊙ ys)
  --   ⊙-makes-slice-tail x [] = lempty
  --   ⊙-makes-slice-tail (a -< cs >-) ((b -< bs >-) ∷ ys) with a ≟ b
  --   ... | yes refl = lstep-here refl (⊕-makes-slicesˡ bs cs) (lies-in-refl ys)
  --   ... | no     _ = lstep-here refl (lies-in-refl bs) (⊙-makes-slice-tail (a -< cs >-) ys)

  --   ⊙-makes-slice-head : ∀ {i} (x : FSTA i) (ys : List (FSTA i))
  --     → x slice-within (x ⊙ ys)
  --   ⊙-makes-slice-head (a -< cs >-) [] = lies-in-refl (a -< cs >- ∷ [])
  --   ⊙-makes-slice-head (a -< cs >-) ((b -< bs >-) ∷ ys) with a ≟ b
  --   ... | yes refl = lstep-here refl (⊕-makes-slicesʳ cs bs) lempty
  --   ... | no   a≠b = lstep-there a≠b (⊙-makes-slice-head (a -< cs >-) ys)

  ⊕-idem : ∀ {i} (xs ys : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → ys ⊕ xs ⊕ ys ≡ xs ⊕ ys
  ⊕-idem xs [] (u-xs , _) _ = ⊕-idˡ xs u-xs
  ⊕-idem [] (y ∷ ys) ([] , []) (y∉ys ∷ u-ys , wf-y ∷ wf-ys) = {!!}
  ⊕-idem (x ∷ xs) (y ∷ ys) xs-wf ys-wf = {!!}

  -- Feature Structure Forest
  record FSF : Set₁ where
    constructor _⊚_
    field
      trees : List (FSTA ∞)
      valid : AllWellFormed trees
  open FSF public

  forget-uniqueness : FSF → List (FSTA ∞)
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
  record Feature : Set₁ where
    constructor _::_
    field
      name : Name F
      impl : FSF
  open Feature public

  record SPL : Set₁ where
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

  names : SPL → List (Name F)
  names spl = (map name) (features spl)

  ---- Algebra ----

  𝟘 : FSF
  𝟘 = [] ⊚ ([] , [])

  infixr 7 _⊛_
  _⊛_ : FSF → FSF → FSF
  (l ⊚ u-l) ⊛ (r ⊚ u-r) = (l ⊕ r) ⊚ (⊕-wf u-l u-r)

  ⊛-all : List FSF → FSF
  ⊛-all = foldr _⊛_ 𝟘

  cong-app₂ : ∀ {ℓ} {A C : Set ℓ} {T : A → Set ℓ} {x y : A} {tx : T x} {ty : T y}
    → (f : (a : A) → T a → C)
    → x ≡ y
    → (∀ (a : A) (t u : T a) → t ≡ u)
    → f x tx ≡ f y ty
  cong-app₂ {y = y} {tx = tx} {ty = ty} f refl T-cong = Eq.cong (f y) (T-cong y tx ty)

  l-id : LeftIdentity _≡_ 𝟘 _⊛_
  l-id (ls ⊚ (u-ls , du-ls)) = cong-app₂ _⊚_ (⊕-idˡ ls u-ls) AllWellFormed-deterministic

  r-id : RightIdentity _≡_ 𝟘 _⊛_
  r-id (xs ⊚ (u-xs , ur-xs)) = refl

  data Once {A : Set₁} (P : A → Set) : List A → Set₁ where
    here  : {x : A} → {xs : List A} →    P x →  All (¬_ ∘ P) xs → Once P (x ∷ xs)
    there : {x : A} → {xs : List A} → ¬ (P x) → Once      P  xs → Once P (x ∷ xs)

  contains? : ∀ {i : Size} (xs : List (FSTA i)) (y : FSTA i)
    → Unique xs
    → y ∉ xs ⊎ Once (y ≈_) xs
  contains? [] y [] = inj₁ []
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) with y == x
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | yes y≈x = inj₂ (here y≈x (map-all (λ x≉a' y≈a' → x≉a' (≈-trans (≈-sym y≈x) y≈a')) x∉xs))
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x with contains? xs y xs-unique
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x | inj₁ y∉xs = inj₁ (y≉x ∷ y∉xs)
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x | inj₂ y∈x = inj₂ (there y≉x y∈x)

  ∈-⊙ˡ : ∀ {i : Size} (x : FSTA i) (ys : List (FSTA i)) (z : FSTA i)
    → x ∈ ys
    → x ∈ (ys ⊙ z)
  ∈-⊙ˡ x (y ∷ ys) z (here x≈y) with z == y
  ∈-⊙ˡ x (y ∷ ys) z (here x≈y) | no _ = here x≈y
  ∈-⊙ˡ (x -< _ >-) (.x -< _ >- ∷ ys) (.x -< _ >-) (here refl) | yes refl = here refl
  ∈-⊙ˡ x (y ∷ ys) z (there x∈ys) with z == y
  ∈-⊙ˡ x (y ∷ ys) z (there x∈ys) | no z≉y = there (∈-⊙ˡ x ys z x∈ys)
  ∈-⊙ˡ x (.z -< _ >- ∷ ys) (z -< _ >-) (there x∈ys) | yes refl = there x∈ys

  ∈-⊙ʳ : ∀ {i : Size} (x : FSTA i) (ys : List (FSTA i)) (z : FSTA i)
    → x ≈ z
    → x ∈ (ys ⊙ z)
  ∈-⊙ʳ x [] z x≈z = here x≈z
  ∈-⊙ʳ x (y ∷ ys) z x≈z with z == y
  ∈-⊙ʳ x (y ∷ ys) z x≈z | no z≉y = there (∈-⊙ʳ x ys z x≈z)
  ∈-⊙ʳ (x -< _ >-) ((.x -< _ >-) ∷ ys) (x -< _ >-) refl | yes refl = here refl

  compute-⊙-excludes : ∀ {i : Size} (x : FSTA i) (xs : List (FSTA i)) (y : FSTA i)
    → y ≉ x
    → (x ∷ xs) ⊙ y ≡ x ∷ (xs ⊙ y)
  compute-⊙-excludes x xs y y≉x with y == x
  compute-⊙-excludes x xs y y≉x | yes y≈x = ⊥-elim (y≉x y≈x)
  compute-⊙-excludes x xs y y≉x | no y≉x = refl

  compute-⊙-includes : ∀ {i : Size} (x : A) (cs₁ cs₂ : List (FSTA i)) (ys : List (FSTA (↑ i)))
    → (x -< cs₁ >- ∷ ys) ⊙ (x -< cs₂ >-) ≡ x -< cs₁ ⊕ cs₂ >- ∷ ys
  compute-⊙-includes x cs₁ cs₂ ys with x ≟ x
  compute-⊙-includes x cs₁ cs₂ ys | yes refl = refl
  compute-⊙-includes x cs₁ cs₂ ys | no x≢x = ⊥-elim (x≢x refl)

  reorder-⊙ : ∀ {i : Size} (xs : List (FSTA i)) (y z : FSTA i)
    → y ≉ z
    → z ∈ xs
    → (xs ⊙ z) ⊙ y ≡ (xs ⊙ y) ⊙ z
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs with z == x
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs | yes z≈x with y == x
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs | yes z≈x | yes y≈x = ⊥-elim (y≉z (≈-trans y≈x (≈-sym z≈x)))
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ with y == (z -< cs₁ ⊕ cs₂ >-)
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ with z ≟ z
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ | yes refl = refl
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ | no z≢z = ⊥-elim (z≢z refl)
  reorder-⊙ (.z -< cs₁ >- ∷ xs) (.z -< _ >-) (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | yes refl = ⊥-elim (y≉z refl)
  reorder-⊙ (x ∷ xs) y z y≉z (here z≈x) | no z≉x = ⊥-elim (z≉x z≈x)
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x with y == x
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ with z == x
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ | yes z≈x = ⊥-elim (z≉x z≈x)
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ | no _ = Eq.cong₂ _∷_ refl (reorder-⊙ xs y z y≉z z∈xs)
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) z y≉z (there z∈xs) | no z≉x | yes refl with z == (y -< cs₁ ⊕ cs₂ >-)
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) z y≉z (there z∈xs) | no z≉x | yes refl | no z≉y = refl
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) (.y -< _ >-) y≉z (there z∈xs) | no z≉a | yes refl | yes refl = ⊥-elim (y≉z refl)

  reorder-after-⊕ : ∀ {i : Size} (xs ys : List (FSTA i)) (z : FSTA i)
    → z ∈ xs
    → z ∉ ys
    → xs ⊕ (z ∷ ys) ≡ xs ⊕ (ys ⊙ z)
  reorder-after-⊕ xs [] z z∈xs [] = refl
  reorder-after-⊕ xs (y ∷ ys) z z∈xs (z≉y ∷ z∉ys) =
      xs ⊕ (z ∷ (y ∷ ys))
    ≡⟨⟩
      foldl _⊙_ xs (z ∷ y ∷ ys)
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ z) (y ∷ ys)
    ≡⟨⟩
      foldl _⊙_ ((xs ⊙ z) ⊙ y) ys
    ≡⟨ Eq.cong (λ x → foldl _⊙_ x ys) (reorder-⊙ xs y z (≉-sym z≉y) z∈xs) ⟩
      foldl _⊙_ ((xs ⊙ y) ⊙ z) ys
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ y) (z ∷ ys)
    ≡⟨ reorder-after-⊕ (xs ⊙ y) ys z (∈-⊙ˡ z xs y z∈xs) z∉ys ⟩
      foldl _⊙_ xs (y ∷ (ys ⊙ z))
    ≡⟨ Eq.cong (foldl _⊙_ xs) (compute-⊙-excludes y ys z z≉y) ⟨
      foldl _⊙_ xs ((y ∷ ys) ⊙ z)
    ≡⟨⟩
      xs ⊕ ((y ∷ ys) ⊙ z)
    ∎

  ⊙-⊕-distrib-excludes : ∀ {i : Size} (xs : List (FSTA (↑ i))) (y : A) (cs₁ cs₂ : List (FSTA i))
    → (y -< cs₁ ⊕ cs₂ >-) ∉ xs
    → xs ⊙ (y -< cs₁ ⊕ cs₂ >-) ≡ (xs ⊙ (y -< cs₁ >-)) ⊙ (y -< cs₂ >-)
  ⊙-⊕-distrib-excludes [] y cs₁ cs₂ y∉xs with (y -< cs₁ >-) == (y -< cs₂ >-)
  ⊙-⊕-distrib-excludes [] y cs₁ cs₂ y∉xs | yes refl = refl
  ⊙-⊕-distrib-excludes [] y cs₁ cs₂ y∉xs | no y≉y = ⊥-elim (y≉y refl)
  ⊙-⊕-distrib-excludes (a ∷ xs) y cs₁ cs₂ (y≉a ∷ y∉xs) with (y -< cs₁ ⊕ cs₂ >-) == a
  ⊙-⊕-distrib-excludes (a ∷ xs) y cs₁ cs₂ (y≉a ∷ y∉xs) | yes y≈a = ⊥-elim (y≉a y≈a)
  ⊙-⊕-distrib-excludes (a ∷ xs) y cs₁ cs₂ (y≉a ∷ y∉xs) | no _ =
      a ∷ (xs ⊙ (y -< cs₁ ⊕ cs₂ >-))
    ≡⟨ Eq.cong₂ _∷_ refl (⊙-⊕-distrib-excludes xs y cs₁ cs₂ y∉xs) ⟩
      a ∷ (xs ⊙ (y -< cs₁ >-) ⊙ (y -< cs₂ >-))
    ≡⟨ compute-⊙-excludes a (xs ⊙ y -< cs₁ >-) (y -< cs₂ >-) (≉-ignores-children refl ≈-refl y≉a) ⟨
      (a ∷ (xs ⊙ (y -< cs₁ >-))) ⊙ (y -< cs₂ >-)
    ≡⟨ Eq.cong₂ _⊙_ (compute-⊙-excludes a xs (y -< cs₁ >-) (≉-ignores-children refl ≈-refl y≉a)) refl ⟨
      (a ∷ xs) ⊙ (y -< cs₁ >-) ⊙ (y -< cs₂ >-)
    ∎

  ⊕-assoc : ∀ {i : Size} (xs ys zs : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → AllWellFormed zs
    → xs ⊕ (ys ⊕ zs) ≡ (xs ⊕ ys) ⊕ zs

  ⊙-⊕-distrib-includes : ∀ {i : Size} (xs : List (FSTA (↑ i))) (y : A) (cs₁ cs₂ : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed cs₁
    → AllWellFormed cs₂
    → Once (y -< cs₁ ⊕ cs₂ >- ≈_) xs
    → xs ⊙ (y -< cs₁ ⊕ cs₂ >-) ≡ (xs ⊙ (y -< cs₁ >-)) ⊙ (y -< cs₂ >-)
  ⊙-⊕-distrib-includes (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf (here y≈x y∉xs) with (y -< cs₁ ⊕ cs₂ >-) == x
  ⊙-⊕-distrib-includes (.y -< cs >- ∷ xs) y cs₁ cs₂ (_ , cs-wf ∷ _) cs₁-wf cs₂-wf (here y≈x y∉xs) | yes refl =
      y -< cs ⊕ (cs₁ ⊕ cs₂) >- ∷ xs
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong₂ _-<_>- refl (⊕-assoc cs cs₁ cs₂ cs-wf cs₁-wf cs₂-wf)) refl ⟩
      y -< (cs ⊕ cs₁) ⊕ cs₂ >- ∷ xs
    ≡⟨ compute-⊙-includes y (cs ⊕ cs₁) cs₂ xs ⟨
      (y -< cs ⊕ cs₁ >- ∷ xs) ⊙ (y -< cs₂ >-)
    ≡⟨ Eq.cong₂ _⊙_ (compute-⊙-includes y cs cs₁ xs) refl ⟨
      ((y -< cs >- ∷ xs) ⊙ (y -< cs₁ >-)) ⊙ (y -< cs₂ >-)
    ∎
  ⊙-⊕-distrib-includes (x -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf (here y≈x y∉xs) | no y≉x = ⊥-elim (y≉x y≈x)
  ⊙-⊕-distrib-includes (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf (there y≉x y∈x) with (y -< cs₁ ⊕ cs₂ >-) == x
  ⊙-⊕-distrib-includes (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf (there y≉x y∈x) | yes y≈x = ⊥-elim (y≉x y≈x)
  ⊙-⊕-distrib-includes (x ∷ xs) y cs₁ cs₂ (_ ∷ xs-unique , _ ∷ xs-wf) cs₁-wf cs₂-wf (there y≉x y∈x) | no _ =
      x ∷ (xs ⊙ (y -< cs₁ ⊕ cs₂ >-))
    ≡⟨ Eq.cong₂ _∷_ refl (⊙-⊕-distrib-includes xs y cs₁ cs₂ (xs-unique , xs-wf) cs₁-wf cs₂-wf y∈x) ⟩
      x ∷ (xs ⊙ (y -< cs₁ >-) ⊙ (y -< cs₂ >-))
    ≡⟨ compute-⊙-excludes x (xs ⊙ y -< cs₁ >-) (y -< cs₂ >-) (≉-ignores-children refl ≈-refl y≉x) ⟨
      (x ∷ (xs ⊙ (y -< cs₁ >-))) ⊙ (y -< cs₂ >-)
    ≡⟨ Eq.cong₂ _⊙_ (compute-⊙-excludes x xs (y -< cs₁ >-) (≉-ignores-children refl ≈-refl y≉x)) refl ⟨
      (x ∷ xs) ⊙ (y -< cs₁ >-) ⊙ (y -< cs₂ >-)
    ∎

  ⊙-⊕-distrib : {i : Size} (xs : List (FSTA (↑ i))) (y : A) (cs₁ cs₂ : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed cs₁
    → AllWellFormed cs₂
    → xs ⊙ (y -< cs₁ ⊕ cs₂ >-) ≡ (xs ⊙ (y -< cs₁ >-)) ⊙ (y -< cs₂ >-)
  ⊙-⊕-distrib xs y cs₁ cs₂ (xs-unique , xs-wf) cs₁-wf cs₂-wf =
    Sum.[ ⊙-⊕-distrib-excludes xs y cs₁ cs₂
        , ⊙-⊕-distrib-includes xs y cs₁ cs₂ (xs-unique , xs-wf) cs₁-wf cs₂-wf
        ]′ (contains? xs (y -< cs₁ ⊕ cs₂ >-) xs-unique)

  ⊕-⊙-assoc-excludes : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → z ∉ ys
    → xs ⊕ (ys ⊙ z) ≡ (xs ⊕ ys) ⊙ z
  ⊕-⊙-assoc-excludes xs [] z [] = refl
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) with z == y
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) | yes z≡y = ⊥-elim (z≢y z≡y)
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) | no _ = ⊕-⊙-assoc-excludes (xs ⊙ y) ys z z∉ys

  ⊕-⊙-assoc-includes : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → WellFormed z
    → Once (z ≈_) ys
    → xs ⊕ (ys ⊙ z) ≡ (xs ⊕ ys) ⊙ z
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (here z≈b z∉ys) with z == y
  ⊕-⊙-assoc-includes xs (.z -< cs₁ >- ∷ ys) (z -< cs₂ >-) xs-wf (_ , cs₁-wf ∷ _) z-wf (here z≈b z∉ys) | yes refl =
      xs ⊕ (z -< cs₁ ⊕ cs₂ >- ∷ ys)
    ≡⟨⟩
      foldl _⊙_ xs (z -< cs₁ ⊕ cs₂ >- ∷ ys)
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ (z -< cs₁ ⊕ cs₂ >-)) ys
    ≡⟨ Eq.cong (λ x → foldl _⊙_ x ys) (⊙-⊕-distrib xs z cs₁ cs₂ xs-wf cs₁-wf z-wf) ⟩
      foldl _⊙_ ((xs ⊙ z -< cs₁ >-) ⊙ (z -< cs₂ >-)) ys
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ z -< cs₁ >-) (z -< cs₂ >- ∷ ys)
    ≡⟨ reorder-after-⊕ (xs ⊙ z -< cs₁ >-) ys (z -< cs₂ >-) (∈-⊙ʳ (z -< cs₂ >-) xs (z -< cs₁ >-) refl) z∉ys ⟩
      foldl _⊙_ (xs ⊙ z -< cs₁ >-) (ys ⊙ z -< cs₂ >-)
    ≡⟨ ⊕-⊙-assoc-excludes (xs ⊙ z -< cs₁ >-) ys (z -< cs₂ >-) z∉ys ⟩
      foldl _⊙_ (xs ⊙ z -< cs₁ >-) ys ⊙ (z -< cs₂ >-)
    ≡⟨⟩
      foldl _⊙_ xs (z -< cs₁ >- ∷ ys) ⊙ (z -< cs₂ >-)
    ≡⟨⟩
      (xs ⊕ (z -< cs₁ >- ∷ ys)) ⊙ (z -< cs₂ >-)
    ∎
  ⊕-⊙-assoc-includes xs (y -< cs₁ >- ∷ ys) (z -< cs₂ >-) xs-wf ys-wf z-wf (here z≈b z∉ys) | no z≉b = ⊥-elim (z≉b z≈b)
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (there z≉b z∉ys) with z == y
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (there z≉b z∉ys) | yes z≈b = ⊥-elim (z≉b z≈b)
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf (_ ∷ ys-unique , b-wf ∷ ys-wf) z-wf (there z≉b z∉ys) | no _ = ⊕-⊙-assoc-includes (xs ⊙ y) ys z (⊙-wf xs-wf b-wf) (ys-unique , ys-wf) z-wf z∉ys

  ⊕-⊙-assoc : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → WellFormed z
    → foldl _⊙_ xs (ys ⊙ z) ≡ foldl _⊙_ xs ys ⊙ z
  ⊕-⊙-assoc xs ys z xs-wf (ys-unique , ys-wf) z-wf =
    Sum.[ ⊕-⊙-assoc-excludes xs ys z
        , ⊕-⊙-assoc-includes xs ys z xs-wf (ys-unique , ys-wf) z-wf
        ]′ (contains? ys z ys-unique)

  -- ⊕-assoc : ∀ {i : Size} (xs ys zs : List (FSTA i))
  --   → AllWellFormed xs
  --   → AllWellFormed ys
  --   → AllWellFormed zs
  --   → xs ⊕ (ys ⊕ zs) ≡ (xs ⊕ ys) ⊕ zs
  ⊕-assoc xs ys [] xs-wf ys-wf zs-wf = refl
  ⊕-assoc xs ys (z ∷ zs) xs-wf ys-wf (_ ∷ zs-unique , z-wf ∷ zs-wf) =
      xs ⊕ (ys ⊕ (z ∷ zs))
    ≡⟨⟩
      foldl _⊙_ xs (foldl _⊙_ ys (z ∷ zs))
    ≡⟨⟩
      foldl _⊙_ xs (foldl _⊙_ (ys ⊙ z) zs)
    ≡⟨ ⊕-assoc xs (ys ⊙ z) zs xs-wf (⊙-wf ys-wf z-wf) (zs-unique , zs-wf) ⟩
      foldl _⊙_ (foldl _⊙_ xs (ys ⊙ z)) zs
    ≡⟨ Eq.cong (λ x → foldl _⊙_ x zs) (⊕-⊙-assoc xs ys z xs-wf ys-wf z-wf) ⟩
      foldl _⊙_ (foldl _⊙_ xs ys ⊙ z) zs
    ≡⟨⟩
      foldl _⊙_ (foldl _⊙_ xs ys) (z ∷ zs)
    ≡⟨⟩
      (xs ⊕ ys) ⊕ (z ∷ zs)
    ∎

  -- ⊛ is not commutative because
  -- ⊕ is not commutative because
  -- the order in which children appear below their parents
  -- is swapped.
  -- Example:
  -- X :: a -< b >-
  -- Y :: a -< c >-
  -- X ⊕ Y = a -< b , c >-
  -- Y ⊕ X = a -< c , b >-
  assoc : Associative _≡_ _⊛_
  assoc (x ⊚ x-wf) (y ⊚ y-wf) (z ⊚ z-wf) = cong-app₂ _⊚_ (Eq.sym (⊕-assoc x y z x-wf y-wf z-wf)) AllWellFormed-deterministic

  cong : Congruent₂ _≡_ _⊛_
  cong refl refl = refl

  idem : ∀ (x y : FSF) → y ⊛ x ⊛ y ≡ x ⊛ y
  idem = {!!}

  FST-is-FeatureAlgebra : FeatureAlgebra FSF _⊛_ 𝟘
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
  ⟦_⟧ : SPL → Conf → Rose ∞ AtomSet
  ⟦ r ◀ features ⟧ c = r -< forget-uniqueness (⊛-all (select c features)) >-

  open import Data.String using (String; _<+>_)
  open import Show.Lines hiding (map)

  module Show (show-F : F → String) (show-A : A → String) where
    mutual
      show-FST : FSTA ∞ → Lines
      show-FST = induction λ a children → do
        > show-A a
        indent 2 (lines children)

      show-FSF : List (FSTA ∞) → Lines
      show-FSF roots = lines (map show-FST roots)

      show-Feature : Feature → Lines
      show-Feature feature = do
        > show-F (name feature) <+> "∷"
        indent 2 (show-FSF (forget-uniqueness (impl feature)))

FSTL-Sem : 𝔼-Semantics (Rose ∞) Conf Impose.SPL
FSTL-Sem {A} = Impose.⟦_⟧ A

FSTL : VariabilityLanguage (Rose ∞)
FSTL = ⟪ Impose.SPL , Conf , FSTL-Sem ⟫


module IncompleteOnRose where
  variant-0 = rose-leaf {A = (ℕ , ℕ._≟_)} 0
  variant-1 = rose-leaf {A = (ℕ , ℕ._≟_)} 1

  variants-0-and-1 : VMap (Rose ∞) (ℕ , ℕ._≟_) 1
  variants-0-and-1 zero = variant-0
  variants-0-and-1 (suc zero) = variant-1

  does-not-describe-variants-0-and-1 :
    ∀ {i : Size}
    → (e : Impose.SPL (ℕ , ℕ._≟_))
    → ∃[ c ] (variant-0 ≡ FSTL-Sem e c)
    → ∄[ c ] (variant-1 ≡ FSTL-Sem e c)
  does-not-describe-variants-0-and-1 (zero Impose.◀ features) _ ()
  does-not-describe-variants-0-and-1 (suc root Impose.◀ features) ()

  FST-is-incomplete : Incomplete (Rose ∞) FSTL
  FST-is-incomplete complete with complete variants-0-and-1
  FST-is-incomplete complete | e , e⊆vs , vs⊆e = does-not-describe-variants-0-and-1 e (e⊆vs zero) (e⊆vs (suc zero))

cannotEncodeNeighbors : ∀ {A : 𝔸} (a b : atoms A) → ∄[ e ] (∃[ c ] FSTL-Sem e c ≡ a -< rose-leaf b ∷ rose-leaf b ∷ [] >-)
cannotEncodeNeighbors {A} a b (e , conf , ⟦e⟧c≡neighbors) =
  ¬Unique b (Eq.subst (λ l → Unique l) (children-equality ⟦e⟧c≡neighbors) (lemma (⊛-all (select conf (features e)))))
  where
  open Impose A

  lemma : ∀ (e : FSF) → Unique (forget-uniqueness e)
  lemma (_ Impose.⊚ (unique , _)) = unique

  ¬Unique : ∀ (a : atoms A) → ¬ Unique (a -< [] >- ∷ a -< [] >- ∷ [])
  ¬Unique a ((a≢a ∷ []) ∷ [] ∷ []) = a≢a refl
