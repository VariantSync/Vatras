{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.Definitions

{-
This module formalizes feature structure trees.
We formalized the language, its semantics, and the typing to disallow duplicate neighbors.
We also prove that FSTs are a feature algebra but the proof is work in progress.
-}
module Lang.FST (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; foldr; map; filterᵇ; concat; reverse)
open import Data.List.Properties using (++-identityˡ; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Size using (Size; ↑_; ∞)

open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open Eq.≡-Reasoning

open import Framework.Annotation.Name using (Name)
open import Framework.Variants using (Rose; rose; rose-leaf)
open import Framework.Composition.FeatureAlgebra
open import Framework.VariabilityLanguage
open import Construct.Artifact as At using ()

open import Util.SparseSublist

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

pattern _-<_>- a cs = rose (a At.-< cs >-)
fst-leaf = rose-leaf

induction : ∀ {A : 𝔸} {B : Set} → (atoms A → List B → B) → FST ∞ A → B
induction {A} {B} f n = go n [] where
  go : FST ∞ A → List B → B
  go (a -< [] >-) bs = f a (reverse bs)
  go (a -< c ∷ cs >-) bs = go (a -< cs >-) (go c [] ∷ bs)

infix 15 _≈_
_≈_ : ∀ {A i} → Rel (FST i A) 0ℓ
(a -< _ >-) ≈ (b -< _ >-) = a ≡ b

≈-refl : ∀ {A i} → (a : FST i A) → a ≈ a
≈-refl (_ -< _ >-) = refl

≈-sym : ∀ {A i} → (a b : FST i A) → a ≈ b → b ≈ a
≈-sym (a -< _ >-) (.a -< _ >-) refl = refl

infix 15 _≉_
_≉_ : ∀ {A i} → Rel (FST i A) 0ℓ
a ≉ b = ¬ (a ≈ b)

≉-sym : ∀ {A i} → (a b : FST i A) → a ≉ b → b ≉ a
≉-sym a b a≉b b≈a = a≉b (≈-sym b a b≈a)

infix 15 _∈_
_∈_ : ∀ {i A} → FST i A → List (FST i A) → Set
x ∈ xs = Any (x ≈_) xs

infix 15 _∉_
_∉_ : ∀ {i A} → FST i A → List (FST i A) → Set
x ∉ xs = All (x ≉_) xs

_⊑_ : ∀ {i A} → (xs ys : List (FST i A)) → Set --\squb=
xs ⊑ ys = All (_∈ ys) xs

_⋢_ : ∀ {i A} → (xs ys : List (FST i A)) → Set --\squb=n
xs ⋢ ys = Any (_∉ ys) xs

Disjoint : ∀ {i A} → (xs ys : List (FST i A)) → Set --\squb=n
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
  = (≉-sym r l r≉l ∷ l∉rs) ∷ disjoint-grow r rs ls d-ls-rs r∉ls

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
  FSTA : Size → Set
  FSTA i = FST i AtomSet

  private
    A = atoms AtomSet
    _≟_ = proj₂ AtomSet

  _==_ : ∀ {i} → Decidable (_≈_ {AtomSet} {i})
  (a -< _ >-) == (b -< _ >-) = a ≟ b

  conclude-node-equality : ∀ {i} {a b : A} {as bs : List (FSTA i)}
    → (a -< as >-) ≡ (b -< bs >-)
    → a ≡ b
  conclude-node-equality refl = refl

  -- impossible
  -- ≢→≉ : ∀ {i} {a b : A} {as bs : List (FSTA i)}
  --   → (a -< as >-) ≢ (b -< bs >-)
  --   → (a -< as >-) ≉ (b -< bs >-)
  -- ≢→≉ neq refl = neq {!!}

  ≉→≢ : ∀ {i} {x y : FSTA i}
    → x ≉ y
    → x ≢ y
  ≉→≢ {x = x} nono refl = nono (≈-refl x)

  All≉→All≢ : ∀ {i} {x : FSTA i} {xs : List (FSTA i)}
    → All (_≉ x) xs
    → All (_≢ x) xs
  All≉→All≢ = map-all ≉→≢

  All≉-sym : ∀ {i} {x : FSTA i} {xs : List (FSTA i)}
    → All (x ≉_) xs
    → All (_≉ x) xs
  All≉-sym [] = []
  All≉-sym {x = x} {xs = y ∷ _} (px ∷ pxs) = ≉-sym x y px ∷ All≉-sym pxs

  _==-FST_ : ∀ {i} → DecidableEquality (FSTA i)
  (a -< as >-) ==-FST (b -< bs >-) with a ≟ b
  ... | yes refl = {!!} -- is there a decidable equality on lists we can reuse here?
  ... | no  a≢b  = no (λ eq → a≢b (conclude-node-equality eq))

  -- ≟-refl : ∀ (x : A) → x ≡ x
  -- ≟-refl = {!!}

  mutual
    infixr 5 _⊕_
    _⊕_ : ∀ {i} → List (FSTA i) → List (FSTA i) → List (FSTA i)
    l ⊕ []      = l
    l ⊕ (h ∷ t) = (h ⊙ l) ⊕ t


    infixr 5 _⊙_
    _⊙_ : ∀ {i} → FSTA i → List (FSTA i) → List (FSTA i)
    l ⊙ [] = l ∷ []
    l ⊙ (h ∷ t) with l == h
    ... | no _ = h ∷ (l ⊙ t)
    a -< ca >- ⊙ (.a -< cb >- ∷ t) | yes refl = a -< ca ⊕ cb >- ∷ t

  Unique : ∀ {i} → List (FSTA i) → Set
  Unique = AllPairs _≉_

  mutual
    WellFormed : ∀ {i} → FSTA i → Set
    WellFormed (_ -< cs >-) = AllWellFormed cs

    AllWellFormed : ∀ {i} → List (FSTA i) → Set
    AllWellFormed cs = Unique cs × All WellFormed cs

  mutual
    ⊕-wf : ∀ {i} {ls rs : List (FSTA i)}
      → AllWellFormed ls
      → AllWellFormed rs
      → AllWellFormed (ls ⊕ rs)
    ⊕-wf ls-wf ([] , []) = ls-wf
    ⊕-wf ls-wf (_ ∷ u-rs , du-r ∷ du-rs) = ⊕-wf (⊙-wf du-r ls-wf) (u-rs , du-rs)

    ⊙-wf : ∀ {i} {l : FSTA i} {r : List (FSTA i)}
      → WellFormed l
      → AllWellFormed r
      → AllWellFormed (l ⊙ r)
    ⊙-wf du-l ([] , []) = [] ∷ [] , du-l ∷ []
    ⊙-wf {_} {l} {h ∷ _} _ (_ ∷ _ , _ ∷ _) with l == h
    ⊙-wf {_} {a -< ca >- } {(.a -< cb >-) ∷ t} wf-ca (  _ ∷ _   , wf-cb ∷    _) | yes refl with ⊕-wf wf-ca wf-cb
    ⊙-wf                                       _     (u-h ∷ u-t ,     _ ∷ du-t) | yes refl | wf-ca⊕cb
      = (map-∉ u-h) ∷ u-t , wf-ca⊕cb ∷ du-t
    ⊙-wf {_} {a -< ca >- } {b -< cb >- ∷ t} du-l (u-h ∷ u-t , du-h ∷ du-t) | no _ with ⊙-wf du-l (u-t , du-t)
    ⊙-wf {_} {a -< ca >- } {b -< cb >- ∷ t} du-l (u-h ∷ u-t , du-h ∷ du-t) | no a≢b | u-rec , du-rec
      = ind a≢b u-h ∷ u-rec , du-h ∷ du-rec
      where
        ind :  ∀ {i} {b a} {cb ca : List (FSTA i)} {t : List (FSTA (↑ i))}
          → ¬ (a ≡ b)
          → b -< cb >- ∉ t
          → b -< cb >- ∉ ((a -< ca >-) ⊙ t)
        ind {t = []} a≢b b∉t = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ []
        ind {_} {_} {a} {_}  {ca} {t ∷ ts} a≢b b∉t with (a -< ca >-) == t
        ind {_} {_} {a} {cb} {ca} {(.a -< ct >-) ∷ ts} a≢b (  _ ∷ b∉ts) | yes refl = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ b∉ts
        ind {_} {_} {a} {cb} {ca} {( t -< ct >-) ∷ ts} a≢b (b≢t ∷ b∉ts) | no   a≢t = b≢t ∷ (ind a≢b b∉ts)

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
    → l ⊙ rs ≡ rs ∷ʳ l
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
-- Goal: (r ⊙ ls) ⊕ rs ≡ ls ++ r ∷ rs
    rewrite (Eq.sym (lem r rs ls))
-- Goal: (r ⊙ ls) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    rewrite ⊙-stranger r ls r∉ls
-- Goal: (ls ++ r ∷ []) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    = ⊕-strangers (ls ++ r ∷ []) rs u-rs (disjoint-shiftʳ r ls rs (disjoint-grow r ls rs d-ls-rs r∉rs))

  ⊕-idˡ :
    ∀ {i} (rs : List (FSTA i))
    → Unique rs
    → [] ⊕ rs ≡ rs
  ⊕-idˡ rs u-rs = ⊕-strangers [] rs u-rs (disjoint-[]ʳ rs)

  mutual
    -- A proof that an FST x was already imposed into a list of FSTs ys.
    data _imposed-in_ : ∀ {i} → FSTA i → List (FSTA i) → Set where
      lies-here : ∀ {i} {a : A} {as bs : List (FSTA i)} {ys : List (FSTA (↑ i))}
        → All (_imposed-in bs) as
          --------------------------------------
        → (a -< as >-) imposed-in (a -< bs >- ∷ ys)

      lies-there : ∀ {i} {x y : FSTA i} {ys : List (FSTA i)}
        → x ≉ y
        → x imposed-in ys
          ------------------
        → x imposed-in (y ∷ ys)

    -- data _all-imposed-in_ : ∀ {i} → (xs ys : List (FSTA i)) → Set where
    --   all-empty : ∀ {i} (ys : List (FSTA i))
    --     → [] all-imposed-in ys

    --   all-step : ∀ {i} (x : FSTA i) (xs ys : List (FSTA i))
    --     → x imposed-in ys
    --     → xs all-imposed-in ys
    --     → (x ∷ xs) all-imposed-in ys

    _all-imposed-in_ : ∀ {i} → (xs ys : List (FSTA i)) → Set
    xs all-imposed-in ys = All (_imposed-in ys) xs

  _slice-of_ : ∀ {i} → FSTA i → FSTA i → Set
  x slice-of y = x imposed-in (y ∷ [])

  mutual
    imposed-in-refl : ∀ {i} (x : FSTA i) (ys : List (FSTA i))
      → WellFormed x
      → AllWellFormed ys
      → x in-list ys
      → x imposed-in ys
    imposed-in-refl (a -< as >-) ((.a -< .as >-) ∷ ys) wx wys (step-match asd)
      = lies-here (all-imposed-in-refl as as wx wx (sparse-sublist-refl as))
    imposed-in-refl (a -< as >-) ((b -< bs >-) ∷ ys) wx (b∉ys ∷ u-ys , wf-bs ∷ wf-ys) (step-diff aas≢bbs asd)
      = lies-there {!aas≢bbs!} (imposed-in-refl (a -< as >-) ys wx (u-ys , wf-ys) asd)
      -- This hole here is difficult to prove. We cannot simply conclude that to unequal FSTs must have unequal atoms.

    all-imposed-in-refl : ∀ {i} (xs ys : List (FSTA i))
      → AllWellFormed xs
      → AllWellFormed ys
      → xs is-sparse-sublist-of ys
      → xs all-imposed-in ys
    all-imposed-in-refl [] _ _ _ _ = []
    all-imposed-in-refl (x ∷ xs) (.x ∷ ys) (x∉xs ∷ u-xs , wf-x ∷ wf-xs) wf-ys (step-match xs-sub-ys)
      = imposed-in-refl x (x ∷ ys) wf-x wf-ys (step-match sub-base) ∷ all-imposed-in-refl xs (x ∷ ys) (u-xs , wf-xs) wf-ys (step-diff' (All≉→All≢ (All≉-sym x∉xs)) xs-sub-ys)
    all-imposed-in-refl {i} (x ∷ xs) (y ∷ ys) (x∉xs ∷ u-xs , wf-x ∷ wf-xs) wf-ys (step-diff x≢y xxs-sub-ys)
      = imposed-in-refl x (y ∷ ys) wf-x wf-ys (step-diff x≢y (sparse-sublist-head x xs ys xxs-sub-ys)) ∷ all-imposed-in-refl xs (y ∷ ys) (u-xs , wf-xs) wf-ys (step-any {FSTA i , _==-FST_} y (drop-head {FSTA i , _==-FST_} xxs-sub-ys))

  mutual
    ⊙-preserves : ∀ (x : FSTA ∞) (ys : List (FSTA ∞))
      → WellFormed x
      → AllWellFormed ys
      → x imposed-in (x ⊙ ys)
    ⊙-preserves x [] wf-x wf-ys = imposed-in-refl x (x ∷ []) wf-x (([] ∷ []) , wf-x ∷ []) (sparse-sublist-refl (x ∷ []))
    ⊙-preserves (a -< as >-) (b  -< bs >- ∷ _) _ _ with a ≟ b
    ⊙-preserves (a -< as >-) ((a -< bs >-) ∷ ys) wf-as (_ , wf-bs ∷ _) | yes refl = lies-here (⊕-preserves as bs wf-as wf-bs)
    ⊙-preserves (a -< as >-) ((b -< bs >-) ∷ ys) wf-x (b∉ys ∷ u-ys , wf-bs ∷ wf-ys) | no a≠b = lies-there a≠b (⊙-preserves (a -< as >-) ys wf-x (u-ys , wf-ys))

    ⊕-preserves : ∀ (xs ys : List (FSTA ∞))
      → AllWellFormed xs
      → AllWellFormed ys
      → xs all-imposed-in (xs ⊕ ys)
    ⊕-preserves xs [] wf-xs wf-ys = all-imposed-in-refl xs xs wf-xs wf-xs (sparse-sublist-refl xs)
    ⊕-preserves [] (y ∷ ys) wf-xs wf-ys = []
    ⊕-preserves (x ∷ xs) (y ∷ ys) wf-xs wf-ys = {!!}

  -- mutual
  --   ⊕-makes-slicesˡ : ∀ {i} (xs ys : List (FSTA i))
  --     → xs imposed-in (ys ⊕ xs)
  --   ⊕-makes-slicesˡ [] ys = lempty
  --   ⊕-makes-slicesˡ (x ∷ xs) ys = slice-concat xs (⊙-makes-slice-head x ys)

  --   ⊕-makes-slicesʳ : ∀ {i} (xs ys : List (FSTA i))
  --     → xs imposed-in (xs ⊕ ys)
  --   ⊕-makes-slicesʳ xs []       = imposed-in-refl xs
  --   ⊕-makes-slicesʳ xs (y ∷ ys) = slice-prop ys (⊙-makes-slice-tail y xs)

  --   ⊙-makes-slice-tail : ∀ {i} (x : FSTA i) (ys : List (FSTA i))
  --     → ys imposed-in (x ⊙ ys)
  --   ⊙-makes-slice-tail x [] = lempty
  --   ⊙-makes-slice-tail (a -< cs >-) ((b -< bs >-) ∷ ys) with a ≟ b
  --   ... | yes refl = lstep-here refl (⊕-makes-slicesˡ bs cs) (imposed-in-refl ys)
  --   ... | no     _ = lstep-here refl (imposed-in-refl bs) (⊙-makes-slice-tail (a -< cs >-) ys)

  --   ⊙-makes-slice-head : ∀ {i} (x : FSTA i) (ys : List (FSTA i))
  --     → x slice-within (x ⊙ ys)
  --   ⊙-makes-slice-head (a -< cs >-) [] = imposed-in-refl (a -< cs >- ∷ [])
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
  record FSF : Set where
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

  cong-app₂ : ∀ {A C : Set} {T : A → Set} {x y : A} {tx : T x} {ty : T y}
    → (f : (a : A) → T a → C)
    → x ≡ y
    → (∀ (a : A) (t u : T a) → t ≡ u)
    → f x tx ≡ f y ty
  cong-app₂ {y = y} {tx = tx} {ty = ty} f refl T-cong = Eq.cong (f y) (T-cong y tx ty)

  l-id : LeftIdentity _≡_ 𝟘 _⊛_
  l-id (ls ⊚ (u-ls , du-ls)) = cong-app₂ _⊚_ (⊕-idˡ ls u-ls) AllWellFormed-deterministic

  r-id : RightIdentity _≡_ 𝟘 _⊛_
  r-id (xs ⊚ (u-xs , ur-xs)) = refl

  -- ⊛ is not commutative because
  -- ⊕ is not commutative because
  -- the order in which children appear below their parents
  -- is swapped.
  -- Example:
  -- X :: a -< b >-
  -- Y :: a -< c >-
  -- X ⊕ Y = a -< b , c >-
  -- Y ⊕ X = a -< c , b >-

  -- ⊙-assoc : ∀ (x y : List (FSTA ∞)) (z : FSTA ∞) → (z ⊙ x) ⊙ y ≡ x ⊙ (z ⊙ y)
  -- ⊙-assoc = {!!}

  time-of-imposition-irrelevant : ∀ (i : FSTA ∞) (x y : List (FSTA ∞))
    → (i ⊙ x) ⊕ y ≡ i ⊙ (x ⊕ y)
  time-of-imposition-irrelevant i x [] = refl
  time-of-imposition-irrelevant (ai -< ci >-) x ((ay -< cy >-) ∷ ys) with ai ≟ ay
  ... | yes refl = {!!}
  ... | no ¬p = {!!}
    -- where
    --   h : (y ⊙ (i ⊙ x)) ⊕ ys ≡ i ⊙ ((y ⊙ x) ⊕ ys)
    --   h = {!!}

  lemxx  : ∀ (x y : List (FSTA ∞)) (z : FSTA ∞) (zs : List (FSTA ∞))
    → (z ⊙ (x ⊕ y)) ⊕ zs ≡ x ⊕ ((z ⊙ y) ⊕ zs)
  lemxx x y z zs = {!!}

  ⊕-assoc : Associative _≡_ _⊕_
  ⊕-assoc x y [] = refl
  ⊕-assoc x y (z ∷ zs) = lemxx x y z zs

  {-
  FSTs should be associate
  -}
  assoc : Associative _≡_ _⊛_
  assoc (x ⊚ x-wf) (y ⊚ y-wf) (z ⊚ z-wf) = {!!}

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
