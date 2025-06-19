open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; NAT)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false)
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Data.Prop
open import Vatras.Framework.Variants using (Forest; Variant-is-VL; encode-idemp; rose-leaf; forest-leaf; forest-singleton; _-<_>-)
open import Vatras.Lang.ADT (Prop F) Forest as ADT using (ADT; ADTL; leaf; _⟨_,_⟩)
-- open import Vatras.Lang.ADT.Pushdown (Prop F) Forest _-<_>-∷[]
open import Vatras.Lang.VT F as VT using (VT; UnrootedVT; _-<_>-; if-true[_]; if[_]then[_]; if[_]then[_]else[_]; vt-leaf)

-- translate-all : ∀ {A} → List (UnrootedVT A) → List (ADT A)
-- translate-all []                               = []
-- translate-all (a -< l >- ∷ xs)                 = push-down-artifact a {!l xs!} ∷ translate-all xs
-- translate-all (if[ p ]then[ x ] ∷ xs)          = p ⟨ translate-all (x ++ xs) , translate-all xs ⟩ ∷ []
-- translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-all l , translate-all r ⟩ ∷ translate-all xs

-- translate : ∀ {A} → VT A → ADT A
-- translate if-true[ l ] = translate-all l

-- TODO: make naming consistent
VTConf = VT.Conf
ADTConf = ADT.Configuration

module _ {A : 𝔸} where
  -- artifact atom, artifact children, artifact neighbors
  pushy : atoms A → ADT A → ADT A → ADT A
  pushy a (D ⟨ l , r ⟩) n             = D ⟨ pushy a l n , pushy a r n ⟩
  pushy a (leaf v)      (leaf v')     = leaf (a -< v >- ∷ v')
  pushy a c@(leaf v)    (D ⟨ l , r ⟩) = D ⟨ pushy a c l , pushy a c r ⟩

  {-# TERMINATING #-}
  translate-all : List (UnrootedVT A) → ADT A
  translate-all []                               = leaf []
  translate-all (a -< l >- ∷ xs)                 = pushy a (translate-all l) (translate-all xs)
  translate-all (if[ p ]then[ l ] ∷ xs)          = p ⟨ translate-all (l ++ xs) , translate-all xs ⟩
  translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-all (l ++ xs) , translate-all (r ++ xs) ⟩

  translate : VT A → ADT A
  translate if-true[ xs ] = translate-all xs

conf : VTConf → ADTConf
conf c p = eval p c

{-|
Fnoc does not work this way.
We implicitly assume here that the given ADTConf does not reason on the syntax of c but only on its semantics (eval).
-}
fnoc : ADTConf → VTConf
fnoc c v = c (var v)

conf-preserves : ∀ (c : VTConf) (p : Prop F) →
  eval p c ≡ (conf c) p
conf-preserves c p = refl

fnoc-preserves : ∀ (c : ADTConf) (p : Prop F) → 
  eval p (fnoc c) ≡ c p
fnoc-preserves c true = {!!}
fnoc-preserves c false = {!!}
fnoc-preserves c (var x) = refl
fnoc-preserves c (¬ p) = {!!}
fnoc-preserves c (p ∧ p₁) = {!!}

module Test {A : 𝔸} where
  module Forest (a b : atoms A) where
    vt : VT A
    vt =
      if-true[
        vt-leaf a ∷ vt-leaf b ∷ []
      ]
  
    adt : ADT A
    adt = leaf (rose-leaf a ∷ rose-leaf b ∷ [])
  
    tr : translate vt ≡ adt
    tr = refl
  
    presˡ : ∀ c → VT.⟦ vt ⟧ c ≡ ADT.⟦ translate vt ⟧ (conf c)
    presˡ _ = refl

    presʳ : ∀ c → VT.⟦ vt ⟧ (fnoc c) ≡ ADT.⟦ translate vt ⟧ c
    presʳ _ = refl
  
  module SingleOption (X : Prop F) (a b : atoms A) where
    vt : VT A
    vt =
      if-true[
        a -<
          if[ X ]then[
            vt-leaf b ∷ []
          ] ∷ []
        >- ∷ []
      ]

    adt : ADT A
    adt = X ⟨ leaf (forest-singleton a (forest-leaf b)) , leaf (forest-leaf a) ⟩
  
    tr : translate vt ≡ adt
    tr = refl

    presˡ-t : ∀ c → VT.⟦ vt ⟧ c ≡ ADT.⟦ translate vt ⟧ (conf c)
    presˡ-t c rewrite conf-preserves c X = {!!}

    -- presˡ-f : VT.⟦ vt ⟧ vtc-f ≡ ADT.⟦ translate vt ⟧ (conf vtc-f)
    -- presˡ-f rewrite vtc-f-all X = refl

    -- presʳ-t : VT.⟦ vt ⟧ (fnoc atc-t) ≡ ADT.⟦ translate vt ⟧ atc-t
    -- presʳ-t rewrite atc-t-all X | vtc-t-all X = refl

    -- presʳ-f : VT.⟦ vt ⟧ (fnoc atc-f) ≡ ADT.⟦ translate vt ⟧ atc-f
    -- presʳ-f rewrite atc-f-all X | vtc-f-all X = refl

