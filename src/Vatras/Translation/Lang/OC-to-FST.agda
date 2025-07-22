{-|
This module provides an example of neighboring artifacts with equal atoms and
uses the `cannotEncodeNeighbors` lemma from `FST` to show that there are
expressions in `WFOC` that cannot be encoded in `FST`.
-}
open import Vatras.Framework.Definitions using (𝔽; 𝔸; NAT')

module Vatras.Translation.Lang.OC-to-FST (F : 𝔽) where

open import Size using (∞)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; _≟_; ℕ)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq

open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All
open OC using (WFOC; Root; _-<_>-; WFOCL)
open FST using (FSTL)
open import Vatras.Lang.FST.Properties using (cannotEncodeNeighbors)

V = Rose ∞
open import Vatras.Framework.Relation.Expressiveness V using (_⋡_)

neighbors : WFOC F ∞ NAT'
neighbors = Root zero (zero -< [] >- ∷ zero -< [] >- ∷ [])

FST⋡WFOC : FSTL F ⋡ WFOCL F
FST⋡WFOC FST≽WFOC with FST≽WFOC neighbors
... | e , e⊆neighbors , neighbors⊆e with e⊆neighbors (λ a → true)
... | conf , e≡neighbors = cannotEncodeNeighbors zero zero (e , conf , Eq.sym e≡neighbors)
