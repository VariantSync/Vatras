open import Vatras.Framework.Definitions
module Vatras.Lang.VT (F : 𝔽) where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; _++_)

open import Vatras.Data.Prop using (Prop; Assignment; eval)
open import Vatras.Framework.Variants using (Forest; _-<_>-)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; ⟪_,_,_⟫)

Configuration : Set
Configuration = Assignment F

data UnrootedVT : 𝔼 where
  _-<_>- : ∀ {A}
    → (a : atoms A)
    → (l : List (UnrootedVT A))
    → UnrootedVT A

  if[_]then[_] : ∀ {A}
    → (p : Prop F)
    → (l : List (UnrootedVT A))
    → UnrootedVT A

  if[_]then[_]else[_] : ∀ {A}
    → (p : Prop F)
    → (l : List (UnrootedVT A))
    → (r : List (UnrootedVT A))
    → UnrootedVT A

data VT : 𝔼 where
  if-true[_] : ∀ {A} → (l : List (UnrootedVT A)) → VT A

vt-leaf : ∀ {A} → atoms A → UnrootedVT A
vt-leaf a = a -< [] >-

mutual
  {-|
  Corresponds to ⟦_⟧* from the dissertation of Paul Bittner.
  To prove termination and to simplify proofs, this definition is an inlined variant of
    configure-all c ts = concatMap (configure c) ts
  -}
  configure-all : ∀ {A} → Configuration → List (UnrootedVT A) → Forest A
  configure-all c [] = []
  configure-all c (x ∷ xs) = configure c x ++ configure-all c xs

  {-|
  Corresponds to ⟦_⟧ on artifacts, options, and choices from the dissertation of Paul Bittner.
  -}
  configure : ∀ {A} → Configuration → UnrootedVT A → Forest A
  configure c (a -< cs >-)        = a -< configure-all c cs >- ∷ []
  configure c (if[ p ]then[ t ])  =
    if (eval p c)
    then configure-all c t
    else []
  configure c (if[ p ]then[ t ]else[ e ]) =
    if (eval p c)
    then configure-all c t
    else configure-all c e

{-|
Corresponds to ⟦_⟧ on the root term from the dissertation of Paul Bittner.
-}
⟦_⟧ : ∀ {A} → VT A → Configuration → Forest A
⟦ if-true[ x ] ⟧ c = configure-all c x

VTL : VariabilityLanguage Forest
VTL = ⟪ VT , Configuration , ⟦_⟧ ⟫
