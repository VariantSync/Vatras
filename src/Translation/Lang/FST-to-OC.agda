open import Framework.Definitions
module Translation.Lang.FST-to-OC (F : 𝔽) where

open import Size using (Size; ↑_; _⊔ˢ_; ∞)

open import Data.Nat using (_≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Variants using (Rose; RoseVL; rose; Artifact∈ₛRose; rose-leaf)

V = Rose ∞
mkArtifact = Artifact∈ₛRose
Option = F

open import Framework.Relation.Expressiveness

open import Framework.VariabilityLanguage
open import Construct.Artifact as At using ()
import Lang.FST as FST
open FST F using (FST; FSTL)

data FeatureName : Set where
  X : FeatureName
  Y : FeatureName

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (zero; suc; ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Framework.VariantMap (ℕ , _≟_)

import Lang.All
open Lang.All.OC using (OC; _❲_❳; WFOC; Root; opt; Configuration; ⟦_⟧; WFOCL)

AtomSet : 𝔸
AtomSet = ℕ , _≟_

open FST FeatureName using (_．_)
open FST.Impose FeatureName AtomSet using (SPL; _◀_; _::_; _⊚_) renaming (⟦_⟧ to FST⟦_⟧)

open import Data.EqIndexedSet
open import Data.Empty using (⊥-elim)

open import Data.Product using (_,_; ∃-syntax)
open import Util.Existence using (¬Σ-syntax)

counterexample-Rose : IndexedSet {Rose ∞ AtomSet} (Fin (suc 3))
counterexample-Rose zero                   = rose-leaf 0
counterexample-Rose (suc zero)             = rose (0 At.-< rose (1 At.-< rose-leaf 2 ∷ [] >-) ∷ [] >-)
counterexample-Rose (suc (suc zero))       = rose (0 At.-< rose (1 At.-< rose-leaf 3 ∷ [] >-) ∷ [] >-)
counterexample-Rose (suc (suc (suc zero))) = rose (0 At.-< rose (1 At.-< rose-leaf 2 ∷ rose-leaf 3 ∷ [] >-) ∷ [] >-)

counterexample-Variant : IndexedSet {Variant AtomSet} (Fin (suc 3))
counterexample-Variant i = Semantics RoseVL (counterexample-Rose i) tt

open import Relation.Nullary.Negation using (¬_)


illegal : ∀ {i : Size} → ∄[ e ∈ WFOC FeatureName i AtomSet ] (⟦ e ⟧ ≅ counterexample-Variant)
-- root must be zero because it is always zero in counterexample-Variant
illegal (Root (suc i) cs , _ , ⊇) with ⊇ zero
... | ()
-- there must be a child because there are variants in counterexample-Variant with children below the root (e.g., suc zero)
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
  (X :: (1 ． 2 ． []) ⊚ ([] ∷ [] , ([] ∷ [] , ([] , []) ∷ []) ∷ [])) ∷
  (Y :: (1 ． 3 ． []) ⊚ ([] ∷ [] , ([] ∷ [] , ([] , []) ∷ []) ∷ [])) ∷
  [])

cef-describes-counterexample : FST⟦ cef ⟧ ≅ counterexample-Rose
cef-describes-counterexample = ⊆[]→⊆ cef-⊆[] , ⊆[]→⊆ {f = fnoc} cef-⊇[]
  where
    conf : FST.Conf FeatureName → Fin 4
    conf c with c X | c Y
    ... | false | false = zero
    ... | false | true  = suc (suc zero)
    ... | true  | false = suc zero
    ... | true  | true  = suc (suc (suc zero))

    cef-⊆[] : FST⟦ cef ⟧ ⊆[ conf ] counterexample-Rose
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

    cef-⊇[] : counterexample-Rose ⊆[ fnoc ] FST⟦ cef ⟧
    cef-⊇[] zero = refl
    cef-⊇[] (suc zero) = refl
    cef-⊇[] (suc (suc zero)) = refl
    cef-⊇[] (suc (suc (suc zero))) = {!!}

ouch : WFOCL FeatureName ⋡ FSTL
ouch sure = {!!}
