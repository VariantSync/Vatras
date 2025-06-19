open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; NAT)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false)
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

open import Vatras.Data.Prop
open import Vatras.Framework.Variants using (Forest; Variant-is-VL; encode-idemp; rose-leaf; forest-leaf; forest-singleton; _-<_>-)
open import Vatras.Lang.ADT (Prop F) Forest as ADT using (ADT; ADTL; leaf; _⟨_,_⟩)
open import Vatras.Lang.ADT.Prop F Forest
-- open import Vatras.Lang.ADT.Pushdown (Prop F) Forest _-<_>-∷[]
open import Vatras.Lang.VT F as VT using (VT; UnrootedVT; _-<_>-; if-true[_]; if[_]then[_]; if[_]then[_]else[_]; vt-leaf)

-- translate-all : ∀ {A} → List (UnrootedVT A) → List (ADT A)
-- translate-all []                               = []
-- translate-all (a -< l >- ∷ xs)                 = push-down-artifact a {!l xs!} ∷ translate-all xs
-- translate-all (if[ p ]then[ x ] ∷ xs)          = p ⟨ translate-all (x ++ xs) , translate-all xs ⟩ ∷ []
-- translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-all l , translate-all r ⟩ ∷ translate-all xs

-- translate : ∀ {A} → VT A → ADT A
-- translate if-true[ l ] = translate-all l

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
  
    pres : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres _ = refl

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

    pres-t : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres-t c with eval X c
    ... | true  = refl
    ... | false = refl

  module SingleChoice (X : Prop F) (a b₁ b₂ e₁ e₂ : atoms A) where
    vt : VT A
    vt =
      if-true[
        a -<
          if[ X ]then[
            vt-leaf b₁ ∷
            vt-leaf b₂ ∷ []
          ]else[
            vt-leaf e₁ ∷
            vt-leaf e₂ ∷ []
          ] ∷ []
        >- ∷ []
      ]

    adt : ADT A
    adt =
      X ⟨
        leaf (forest-singleton a (rose-leaf b₁ ∷ rose-leaf b₂ ∷ [])) ,
        leaf (forest-singleton a (rose-leaf e₁ ∷ rose-leaf e₂ ∷ []))
      ⟩

    tr : translate vt ≡ adt
    tr = refl

    pres-t : VT.⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
    pres-t c with eval X c
    ... | true  = refl
    ... | false = refl
