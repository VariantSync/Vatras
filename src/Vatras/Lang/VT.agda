open import Vatras.Framework.Definitions
module Vatras.Lang.VT (F : 𝔽) where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; concatMap)

open import Vatras.Data.Prop
open import Vatras.Framework.Variants using (Rose; Forest; _-<_>-)
open import Vatras.Framework.VariabilityLanguage

Conf : Set
Conf = Assignment F

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
  -- corresponds to ⟦_⟧*
  {-# TERMINATING #-}
  configure-all : ∀ {A} → Conf → List (UnrootedVT A) → Forest A
  configure-all c ts = concatMap (configure c) ts

  -- corresponds to ⟦_⟧ on artifacts, options, and choices
  configure :
    ∀ {A} → Conf → UnrootedVT A → Forest A
  configure c (a -< cs >-)        = a -< configure-all c cs >- ∷ []
  configure c (if[ p ]then[ t ])  =
    if (eval p c)
    then configure-all c t
    else []
  configure c (if[ p ]then[ t ]else[ e ]) =
    if (eval p c)
    then configure-all c t
    else configure-all c e

-- corresponds to ⟦_⟧ on the root term
⟦_⟧ : ∀ {A} → VT A → Conf → Forest A
⟦ if-true[ x ] ⟧ c = configure-all c x

VariationTreeVL : VariabilityLanguage Forest
VariationTreeVL = ⟪ VT , Conf , ⟦_⟧ ⟫
