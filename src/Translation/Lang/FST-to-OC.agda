{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Translation.Lang.FST-to-OC (F : 𝔽) where

open import Size using (Size; ↑_; _⊔ˢ_; ∞)

open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Variants using (Rose; rose; Artifact∈ₛRose; rose-leaf)

V = Rose ∞
mkArtifact = Artifact∈ₛRose
Option = F

open import Framework.VariabilityLanguage
open import Construct.Artifact as At using ()
import Lang.FST as FST
-- open FST F using (FST; induction; fst-leaf)

open import Framework.Relation.Expressiveness V

-- module _ {A : 𝔸} (_==_ : DecidableEquality A) where
--   open FST.Impose F _==_ using (SPL; _◀_; Feature; _::_; FSF; _⊚_)

--   -- translate-o : ∀ {i} → A → OC i A → Feature
--   -- translate-o a (b OC.-< cs >-) = {!!}
--   -- translate-o a (O OC.❲ e ❳) = {!!}

--   -- left is base
--   mutual
--     embed : FST A → OC ∞ A
--     embed = induction OC._-<_>-

--     merge-trees : F → List (OC ∞ A) → F → FST A → List (OC ∞ A)
--     merge-trees _ [] P t = P ❲ embed t ❳ ∷ []
--     merge-trees O (a OC.-< as >- ∷ inter) P (b FST.-< bs >-) with a == b
--     ... | yes refl = a OC.-< merge O as P bs >- ∷ inter
--     ... | no  nope = O ❲ a OC.-< as >- ❳ ∷ merge-trees O inter P (b FST.-< bs >-)
--     merge-trees O (Q ❲ e ❳ ∷ inter) P t = Q ❲ e ❳ ∷ merge-trees O inter P t

--     {-# TERMINATING #-}
--     merge : F → List (OC ∞ A) → F → List (FST A) → List (OC ∞ A)
--     merge _ ls _ [] = ls
--     merge O ls P (t ∷ ts) = merge O (merge-trees O ls P t) P ts

--   record Intermediate : Set where
--     constructor _:o:_
--     field
--       name : F
--       children : List (OC ∞ A)

--   translate' : List Intermediate → List (OC ∞ A)
--   translate' [] = []
--   translate' ((_ :o: cs) ∷ []) = cs
--   translate' ((O :o: os) ∷ (P :o: ps) ∷ xs) = translate' ({!merge!} ∷ xs)

--   fromFeature : Feature → Intermediate
--   fromFeature (O :: (ts ⊚ _)) = O :o: map embed ts

--   start : List Feature → List Intermediate
--   start = map fromFeature

--   translate : SPL → WFOC ∞ A
--   translate (a ◀ fs) = Root a (translate' (start fs))

module _ (mkDec : (A : 𝔸) → DecidableEquality A) where
  data FeatureName : Set where
    X : FeatureName
    Y : FeatureName

  open import Data.Bool using (true; false; if_then_else_)
  open import Data.Nat using (zero; suc; ℕ)
  open import Data.Fin using (Fin; zero; suc)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  open import Framework.VariantMap V ℕ

  import Lang.OC
  open Lang.OC FeatureName using (OC; _❲_❳; WFOC; Root; opt; Configuration)
  open Lang.OC.Sem FeatureName V mkArtifact

  open FST FeatureName using (_．_)
  open FST.Impose FeatureName (mkDec ℕ) using (SPL; _◀_; _::_; _⊚_; unq) renaming (⟦_⟧ to FST⟦_⟧)
  open FST.Framework FeatureName mkDec

  open import Data.EqIndexedSet
  open import Data.Empty using (⊥-elim)

  open import Data.Product using (_,_; ∃-syntax)
  open import Util.Existence using (¬Σ-syntax)

  counterexample : VMap 3
  counterexample zero                   = rose-leaf 0
  counterexample (suc zero)             = rose (0 At.-< rose (1 At.-< rose-leaf 2 ∷ [] >-) ∷ [] >-)
  counterexample (suc (suc zero))       = rose (0 At.-< rose (1 At.-< rose-leaf 3 ∷ [] >-) ∷ [] >-)
  counterexample (suc (suc (suc zero))) = rose (0 At.-< rose (1 At.-< rose-leaf 2 ∷ rose-leaf 3 ∷ [] >-) ∷ [] >-)

  -- illegal' : ∀ {i : Size} → ∄[ cs ∈ List (OC i ℕ) ] (⟦ Root zero cs ⟧ ≅ counterexample)
  -- illegal' ([] , fst , snd) with snd (suc zero)
  -- ... | ()
  -- illegal' (x ∷ fst , snd) = {!!}

  -- illegal' : ∀ {i : Size} → ∄[ e ∈ OC i ℕ ] (∃[ O ] (∃[ xs ] (⟦ Root zero (opt O e ∷ xs) ⟧ ≅ counterexample)))
  -- illegal' x = {!!}
  open import Relation.Nullary.Negation using (¬_)

  nodup : ∀ {i : Size} {A : 𝔸} (a : A) (x y : OC i A) (zs : List (OC i A))
    → ¬ (∀ (c : Configuration) → (⟦ Root a (x ∷ y ∷ zs) ⟧ c ≡ rose-leaf a))
  nodup a x y zs sure with sure (λ _ → true)
  nodup a (O ❲ e ❳) y zs sure | asd = {!!}
  -- nodup a (b OC.-< bs >-) y zs sure with sure (λ _ → true)
  -- ... | ()
  -- nodup a (O ❲ e ❳) (b OC.-< bs >-) zs sure with sure (λ _ → false)
  -- ... | ()
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) [] sure = {!!}
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) (z ∷ zs) sure = nodup a (P ❲ f ❳) z zs {!sure!}
  -- nodup a (O ❲ e ❳) y zs (c , sure) with c O
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) []       (c , sure) | false with c P
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) [] (c , refl) | false | false = {!!}
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) []       (c , sure) | false | true  = {!!}
  -- nodup a (O ❲ e ❳) (P ❲ f ❳) (z ∷ zs) (c , sure) | false = nodup a (P ❲ f ❳) z zs (c , sure)
  -- nodup a (O ❲ e ❳) y zs (c , sure) | true  = {!!}

  illegal : ∀ {i : Size} → ∄[ e ∈ WFOC i ℕ ] (⟦ e ⟧ ≅ counterexample)
  -- root must be zero because it is always zero in counterexample
  illegal (Root (suc i) cs , _ , ⊇) with ⊇ zero
  ... | ()
  -- there must be a child because there are variants in counterexample with children below the root (e.g., suc zero)
  illegal (Root zero [] , _ , ⊇) with ⊇ (suc zero) -- illegal' (cs , eq)
  ... | ()
  -- there must be an option at the front because there are variants with zero children (e.g., zero)
  illegal (Root zero (a OC.-< cs >- ∷ _) , _ , ⊇) with ⊇ zero
  ... | ()
  -- there can not be any other children
  illegal (Root zero (O ❲ e ❳ ∷ a OC.-< as >- ∷ xs) , ⊆ , ⊇) = {!!}
  illegal (Root zero (O ❲ e ❳ ∷ P OC.❲ e' ❳ ∷ xs) , ⊆ , ⊇) = {!!}
  -- e can be a chain of options but somewhen, there must be an artifact
  illegal (Root zero (O ❲ e ❳ ∷ []) , ⊆ , ⊇) = {!!}
  --illegal' (e , (O , xs , (⊆ , ⊇)))

  cef : SPL
  cef = 0 ◀ (
    (X :: (1 ． 2 ． []) ⊚ ([] ∷ [] , unq ([] ∷ [] , unq ([] , []) ∷ []) ∷ [])) ∷
    (Y :: (1 ． 3 ． []) ⊚ ([] ∷ [] , unq ([] ∷ [] , unq ([] , []) ∷ []) ∷ [])) ∷
    [])

  cef-describes-counterexample : FST⟦ cef ⟧ ≅ counterexample
  cef-describes-counterexample = ⊆[]→⊆ cef-⊆[] , ⊆[]→⊆ {f = fnoc} cef-⊇[]
    where
      conf : FST.Conf FeatureName → Fin 4
      conf c with c X | c Y
      ... | false | false = zero
      ... | false | true  = suc (suc zero)
      ... | true  | false = suc zero
      ... | true  | true  = suc (suc (suc zero))

      cef-⊆[] : FST⟦ cef ⟧ ⊆[ conf ] counterexample
      cef-⊆[] c with c X | c Y
      ... | false | false = refl
      ... | false | true  = refl
      ... | true  | false = refl
      ... | true  | true  = {!!}

      fnoc : Fin 4 → FST.Conf FeatureName
      fnoc zero X = false
      fnoc zero Y = false
      fnoc (suc zero) X = true
      fnoc (suc zero) Y = false
      fnoc (suc (suc zero)) X = false
      fnoc (suc (suc zero)) Y = true
      fnoc (suc (suc (suc zero))) X = true
      fnoc (suc (suc (suc zero))) Y = true

      cef-⊇[] : counterexample ⊆[ fnoc ] FST⟦ cef ⟧
      cef-⊇[] zero = refl
      cef-⊇[] (suc zero) = refl
      cef-⊇[] (suc (suc zero)) = refl
      cef-⊇[] (suc (suc (suc zero))) = {!!}

  ouch : WFOCL ⋡ FSTL
  ouch sure with sure cef
  ... | e , e≣cef = {!!}
