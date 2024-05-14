open import Framework.Definitions using (𝔽; 𝔸)

module Translation.Lang.OC-to-FST (F : 𝔽) where

open import Size using (∞)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; _≟_; ℕ)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq

open import Framework.Variants using (Rose)
open import Lang.All
open OC using (WFOC; Root; _-<_>-; WFOCL)
open FST using (FSTL; cannotEncodeNeighbors)

V = Rose ∞
open import Framework.Relation.Expressiveness V using (_⋡_)

A : 𝔸
A = ℕ , _≟_

neighbors : WFOC F ∞ A
neighbors = Root zero (zero -< [] >- ∷ zero -< [] >- ∷ [])

FSTL⋡WFOCL : FSTL F ⋡ WFOCL F
FSTL⋡WFOCL FSTL≽WFOCL with FSTL≽WFOCL neighbors
... | e , e⊆neighbors , neighbors⊆e with e⊆neighbors (λ a → true)
... | conf , e≡neighbors = cannotEncodeNeighbors F zero zero (e , conf , Eq.sym e≡neighbors)
