-- TODO: Move to Translation module?
open import Vatras.Framework.Definitions
module Vatras.Lang.VT.Superfluous (F : 𝔽) where

open import Data.List using (List; map; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; fromList)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Vatras.Data.Prop using (Prop)
open import Vatras.Data.Prop.Properties using (Nonconst)
open import Vatras.Lang.VT F

data NonSFL {A} : UnrootedVT A → Set₁ where
  ok-artifact : ∀ {a} {cs : List (UnrootedVT A)}
    → All NonSFL cs
      -------------------------
    → NonSFL (a -< cs >-)

  ok-option : ∀ {p} {cs : List (UnrootedVT A)}
    → All NonSFL cs
    → Nonconst p
      --------------------------
    → NonSFL (if[ p ]then[ cs ])

  ok-choice : ∀ {p} {l r : List (UnrootedVT A)}
    → All NonSFL l
    → All NonSFL r
    → Nonconst p
      ----------------------------------
    → NonSFL (if[ p ]then[ l ]else[ r ])

NonSuperfluous : ∀ {A} → VT A → Set₁
NonSuperfluous (if-true[ xs ]) = All NonSFL xs

NonSuperfluousVT : 𝔸 → Set₁
NonSuperfluousVT A = Σ (VT A) NonSuperfluous

NonSuperfluousUVT : 𝔸 → Set₁
NonSuperfluousUVT A = Σ (UnrootedVT A) NonSFL

{-# TERMINATING #-}
elim : ∀ {A} → UnrootedVT A → NonSuperfluousUVT A
elim (a -< l >-) =
  let l' = map elim l in
  a -< map proj₁ l' >- ,
  ok-artifact (fromList l')
elim if[ p ]then[ l ] = {!!}
elim if[ p ]then[ l ]else[ r ] = {!!}

eliminate-const-annotations : ∀ {A} → VT A → NonSuperfluousVT A
eliminate-const-annotations {A} (if-true[ xs ]) = if-true[ map proj₁ nsfl-xs ] , fromList nsfl-xs
  where
    nsfl-xs : List (NonSuperfluousUVT A)
    nsfl-xs = map elim xs
