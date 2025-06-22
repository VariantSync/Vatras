open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; NAT)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (_,_)
open import Function using (id; _∘_; flip)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; cong; cong₂)
open Eq.≡-Reasoning

open import Vatras.Data.Prop
open import Vatras.Data.EqIndexedSet using (≗→≅[]; ≗→≅)
open import Vatras.Framework.Variants using (Forest; Variant-is-VL; encode-idemp; rose-leaf; forest-leaf; forest-singleton; _-<_>-)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Lang.ADT (Prop F) Forest as ADT using (ADT; ADTL; leaf; _⟨_,_⟩)
open import Vatras.Lang.VT F as VT
open import Vatras.Util.AuxProofs using (if-cong)

open import Vatras.Lang.ADT.Prop F Forest using (⟦_⟧ₚ; PropADTL)
open import Vatras.Lang.ADT.Merge Forest (_++_) as Merge
open Merge.Named (Prop F) using (_⊕_)
open Merge.Prop F using (⊕-specₚ)

open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_)

module _ {A : 𝔸} where
  -- artifact atom, artifact children, artifact neighbors
  pushy : atoms A → ADT A → ADT A → ADT A
  pushy a (leaf v)      (leaf v')     = leaf (a -< v >- ∷ v')
  pushy a c@(leaf v)    (D ⟨ l , r ⟩) = D ⟨ pushy a c l , pushy a c r ⟩
  pushy a (D ⟨ l , r ⟩) n             = D ⟨ pushy a l n , pushy a r n ⟩

  mutual
    translate-both : (l r : List (UnrootedVT A)) → ADT A
    translate-both l r = translate-all l ⊕ translate-all r

    translate-all : List (UnrootedVT A) → ADT A
    translate-all []                               = leaf []
    translate-all (a -< l >- ∷ xs)                 = pushy a (translate-all l) (translate-all xs)
    translate-all (if[ p ]then[ l ] ∷ xs)          = p ⟨ translate-both l xs , translate-all xs ⟩
    translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-both l xs , translate-both r xs ⟩

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

  preserves-all : ∀ (vts : List (UnrootedVT A)) → flip configure-all vts ≗ ⟦ translate-all vts ⟧ₚ
  preserves-all [] c = refl
  preserves-all (a -< l >- ∷ xs) c =
      flip configure-all (a -< l >- ∷ xs) c
    ≡⟨⟩
      a -< configure-all c l >- ∷ configure-all c xs
    ≡⟨ cong (_ ∷_) (preserves-all xs c) ⟩
      a -< configure-all c l >- ∷ ⟦ translate-all xs ⟧ₚ c
    ≡⟨ cong (λ z → a -< z >- ∷ _) (preserves-all l c) ⟩
      a -< ⟦ translate-all l ⟧ₚ c >- ∷ ⟦ translate-all xs ⟧ₚ c
    ≡⟨ pushy-preserves a (translate-all l) (translate-all xs) c ⟨
      ⟦ pushy a (translate-all l) (translate-all xs) ⟧ₚ c
    ∎
  preserves-all (if[ p ]then[ l ] ∷ xs) c with eval p c
  ... | true  =
      configure-all c l ++ configure-all c xs
    ≡⟨ cong₂ _++_ (preserves-all l c) (preserves-all xs c) ⟩
      ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c
    ≡⟨ ⊕-specₚ (translate-all l) (translate-all xs) c ⟨
      ⟦ translate-all l ⊕ translate-all xs ⟧ₚ c
    ≡⟨⟩
      ⟦ translate-both l xs ⟧ₚ c
    ∎
  ... | false = preserves-all xs c
  preserves-all (if[ p ]then[ l ]else[ r ] ∷ xs) c with eval p c -- the cases for the choice alternatives are analogous to the first option case above
  ... | true
    rewrite preserves-all l c
          | preserves-all xs c
          | ⊕-specₚ (translate-all l) (translate-all xs) c
          = refl
  ... | false
    rewrite preserves-all r c
          | preserves-all xs c
          | ⊕-specₚ (translate-all r) (translate-all xs) c
          = refl

  preserves : ∀ (vt : VT A) → ⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
  preserves if-true[ xs ] c = preserves-all xs c

VT→PropADT : LanguageCompiler VariationTreeVL PropADTL
VT→PropADT = record
  { compile = translate
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = ≗→≅[] ∘ preserves
  }

PropADT≽VT : PropADTL ≽ VariationTreeVL
PropADT≽VT e = translate e , ≗→≅ (preserves e)

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
