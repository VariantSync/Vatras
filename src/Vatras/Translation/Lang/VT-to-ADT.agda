open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; NAT)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; cong; cong₂)
open Eq.≡-Reasoning

open import Vatras.Data.Prop
open import Vatras.Framework.Variants using (Forest; Variant-is-VL; encode-idemp; rose-leaf; forest-leaf; forest-singleton; _-<_>-)
open import Vatras.Lang.ADT (Prop F) Forest as ADT using (ADT; ADTL; leaf; _⟨_,_⟩)
open import Vatras.Lang.ADT.Prop F Forest using (⟦_⟧ₚ)
open import Vatras.Lang.VT F as VT using (VT; UnrootedVT; ⟦_⟧; _-<_>-; if-true[_]; if[_]then[_]; if[_]then[_]else[_]; vt-leaf; configure; configure-all)
open import Vatras.Util.AuxProofs using (if-cong)

module _ {A : 𝔸} where
  -- artifact atom, artifact children, artifact neighbors
  pushy : atoms A → ADT A → ADT A → ADT A
  pushy a (leaf v)      (leaf v')     = leaf (a -< v >- ∷ v')
  pushy a c@(leaf v)    (D ⟨ l , r ⟩) = D ⟨ pushy a c l , pushy a c r ⟩
  pushy a (D ⟨ l , r ⟩) n             = D ⟨ pushy a l n , pushy a r n ⟩

  {-# TERMINATING #-}
  translate-all : List (UnrootedVT A) → ADT A
  translate-all []                               = leaf []
  translate-all (a -< l >- ∷ xs)                 = pushy a (translate-all l) (translate-all xs)
  translate-all (if[ p ]then[ l ] ∷ xs)          = p ⟨ translate-all (l ++ xs) , translate-all xs ⟩
  translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-all (l ++ xs) , translate-all (r ++ xs) ⟩

  translate : VT A → ADT A
  translate if-true[ xs ] = translate-all xs

  -- Preservation Proofs --
  
  -- formal specification of pushy: It should create an ADT such that for any configuration c, there is an artifact at the top of left
  pushy-preserves : ∀ a l n c → ⟦ pushy a l n ⟧ₚ c ≡ a -< ⟦ l ⟧ₚ c >- ∷ ⟦ n ⟧ₚ c
  pushy-preserves a (leaf v) (leaf v') c = refl
  pushy-preserves a (D ⟨ l , r ⟩) n c with eval D c
  ... | true  = pushy-preserves a l n c
  ... | false = pushy-preserves a r n c
  pushy-preserves a x@(leaf v) (D ⟨ l , r ⟩) c with eval D c
  ... | true  = pushy-preserves a x l c
  ... | false = pushy-preserves a x r c

  ++-preserves : ∀ l r c → ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all r ⟧ₚ c ≡ ⟦ translate-all (l ++ r) ⟧ₚ c
  ++-preserves [] r c = refl
  ++-preserves (l ∷ ls) [] c =
      ⟦ translate-all (l ∷ ls) ⟧ₚ c ++ ⟦ leaf [] ⟧ₚ c
    ≡⟨⟩
      ⟦ translate-all (l ∷ ls) ⟧ₚ c ++ []
    ≡⟨ ++-identityʳ _ ⟩
      ⟦ translate-all (l ∷ ls) ⟧ₚ c
    ≡⟨ cong (λ x → ⟦ translate-all x ⟧ₚ c) (++-identityʳ (l ∷ ls)) ⟨
      ⟦ translate-all (l ∷ ls ++ []) ⟧ₚ c
    ∎
  ++-preserves ((a -< l >-) ∷ ls) rs@(_ ∷ _) c
    rewrite pushy-preserves a (translate-all l) (translate-all ls) c
    rewrite pushy-preserves a (translate-all l) (translate-all (ls ++ rs)) c
    = cong (a -< ⟦ translate-all l ⟧ₚ c >- ∷_) (++-preserves ls rs c)
  ++-preserves (if[ p ]then[ l ] ∷ ls) (r ∷ rs) c with eval p c
  ... | true  =
      ⟦ translate-all (l ++ ls) ⟧ₚ c ++ ⟦ translate-all (r ∷ rs) ⟧ₚ c
    ≡⟨ ++-preserves (l ++ ls) (r ∷ rs) c ⟩
      ⟦ translate-all ((l ++ ls) ++ r ∷ rs) ⟧ₚ c
    ≡⟨ cong (λ x → ⟦ translate-all x ⟧ₚ c) (++-assoc l ls (r ∷ rs)) ⟩
      ⟦ translate-all (l ++ (ls ++ r ∷ rs)) ⟧ₚ c
    ∎
  ... | false = ++-preserves ls (r ∷ rs) c
  ++-preserves (if[ p ]then[ l ]else[ r ] ∷ ls) (r' ∷ rs') c = {!!}

--   preserves-all : ∀ (vts : List (UnrootedVT A)) → flip configure-all vts ≗ ⟦ translate-all vts ⟧ₚ
--   preserves-all [] c = refl
--   preserves-all ((a -< l >-) ∷ xs) c = {!!}
--   preserves-all (if[ p ]then[ l ] ∷ xs) c with eval p c
--   ... | true  =
--     begin
--       concat (map (configure c) l) ++ concat (map (configure c) xs)
--     ≡⟨⟩
--       flip configure-all l c ++ flip configure-all xs c
--     ≡⟨ cong₂ _++_ (preserves-all l c) (preserves-all xs c) ⟩
--       ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c
--     ≡⟨ ++-preserves l xs c ⟩
--       ⟦ translate-all (l ++ xs) ⟧ₚ c
--     ∎
--   ... | false = preserves-all xs c
--   preserves-all (if[ p ]then[ l ]else[ r ] ∷ xs) c = {!!} -- both cases for eval p c should be analogous to the true case for options

--   preserves : ∀ (vt : VT A) → ⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
--   preserves if-true[ xs ] c = preserves-all xs c

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
