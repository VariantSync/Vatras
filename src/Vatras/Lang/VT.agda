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
  configure-all : ∀ {A} → List (UnrootedVT A) → Configuration → Forest A
  configure-all [] c       = []
  configure-all (x ∷ xs) c = configure x c ++ configure-all xs c

  {-|
  Corresponds to ⟦_⟧ on artifacts, options, and choices from the dissertation of Paul Bittner.
  -}
  configure : ∀ {A} → UnrootedVT A → Configuration → Forest A
  configure (a -< cs >-)       c = a -< configure-all cs c >- ∷ []
  configure (if[ p ]then[ t ]) c =
    if (eval p c)
    then configure-all t c
    else []
  configure (if[ p ]then[ t ]else[ e ]) c =
    if (eval p c)
    then configure-all t c
    else configure-all e c

{-|
Corresponds to ⟦_⟧ on the root term from the dissertation of Paul Bittner.
-}
⟦_⟧ : ∀ {A} → VT A → Configuration → Forest A
⟦ if-true[ x ] ⟧ = configure-all x

VTL : VariabilityLanguage Forest
VTL = ⟪ VT , Configuration , ⟦_⟧ ⟫
