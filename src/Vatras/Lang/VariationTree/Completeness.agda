module Vatras.Lang.VariationTree.Completeness where

import Data.Bool as Bool
open import Data.Fin     using (Fin; fromℕ; toℕ; inject₁)
open import Data.List    using (List; []; _∷_; map; concat)
open import Data.Nat     using (ℕ; _≤_; s≤s; z≤n; _≟_)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (yes; no)

open import Vatras.Framework.Definitions
open import Vatras.Framework.Variants using (Forest; Rose; _-<_>-)
open import Vatras.Data.Prop

open import Size using (∞)

open import Vatras.Lang.VariationTree

{-|
Encodes a tree as a non-variational UnrootedVT.
Configuring the resulting expression will always yield
the input tree.
-}
{-# TERMINATING #-}
encode-tree : ∀ {A F} → Rose ∞ A → UnrootedVT F A
encode-tree (a -< cs >-) = a -< map encode-tree cs >-

{-|
Encodes all trees in a forest to a non-variational
UnrootedVT each, using 'encode-tree' defined above.
-}
encode-forest : ∀ {A F} → Forest A → List (UnrootedVT F A)
encode-forest = map encode-tree

Numbered : Set → Set
Numbered F = F × ℕ

{-|
Removes the last variant from a variant generator
(i.e., the variant at the highest index).
-}
remove-last : ∀ {A n}
  → (Fin (ℕ.suc n) → Forest A)
  → (Fin n         → Forest A)
remove-last set i = set (inject₁ i)

module _ (F : 𝔽) (x : F) where
  {-|
  Encodes a non-empty variant generator as a list
  of variation trees.
  -}
  encode' : ∀ {A} (n : ℕ)
    → 1 ≤ n
    → (Fin n → Forest A)
    → List (UnrootedVT (Numbered F) A)
  encode' (ℕ.suc ℕ.zero)    (s≤s z≤n) V = encode-forest (V Fin.zero)
  encode' (ℕ.suc (ℕ.suc n)) (s≤s z≤n) V =
    if[ var (x , ℕ.suc n) ]then[
      encode-forest (V (fromℕ (ℕ.suc n)))
    ]else[
      encode' (ℕ.suc n) (s≤s z≤n) (remove-last V)
    ] ∷ []

  {-|
  Encodes a variant generator of forests
  as a variation tree.
  -}
  encode : ∀ {A} (n : ℕ)
    → (Fin n → Forest A)
    → VT (Numbered F) A
  encode ℕ.zero    V = if-true[ [] ]
  encode (ℕ.suc n) V = if-true[ encode' (ℕ.suc n) (s≤s z≤n) V ]

  conf : ∀ {n} → Fin n → Config (Numbered F)
  conf Fin.zero    (x , j) = Bool.false
  conf (Fin.suc i) (x , j) with toℕ (Fin.suc i) ≟ j
  ... | yes _ = Bool.true
  ... | no  _ = Bool.false

  fnoc : ∀ {n} → Fin n → Config (Numbered F) → Fin n
  fnoc Fin.zero     c = Fin.zero
  fnoc (Fin.suc j)  c with c (x , toℕ (Fin.suc j))
  ... | Bool.true  = Fin.suc j
  ... | Bool.false = inject₁ (fnoc j c)
