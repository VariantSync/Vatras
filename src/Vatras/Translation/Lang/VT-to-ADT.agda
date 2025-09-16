open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Translation.Lang.VT-to-ADT (F : 𝔽) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Function using (id; _∘_; flip)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; cong; cong₂)
open Eq.≡-Reasoning

open import Vatras.Data.Prop using (Prop; eval)
open import Vatras.Data.EqIndexedSet using (≗→≅[])
open import Vatras.Framework.Variants using (Forest; _-<_>-)
open import Vatras.Framework.Compiler as Compiler using (LanguageCompiler)

open import Vatras.Lang.ADT F Forest using (ADTL)
open import Vatras.Lang.ADT.Prop F Forest using (PropADT; PropADTL; ⟦_⟧ₚ; leaf; _⟨_,_⟩)
open import Vatras.Lang.VT F as VT

import Vatras.Lang.ADT.Merge Forest (_++_) as Merge
open Merge.Prop F

open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_; ≽-trans; expressiveness-from-compiler)
open import Vatras.Translation.Lang.ADT.PropSemantics F Forest using (formula-elim-compiler; ADT≽PropADT)

-- artifact atom, artifact children, artifact neighbors
{-|
This function creates an ADT such that the given atom is at the top of all variants described
by the first given ADT (i.e., these are supposed to be children of the atom), with the variants in the
second ADT being the right neighbors.
For a formal specification, see push-down-left-spec below.
-}
push-down-left : ∀ {A} → atoms A → PropADT A → PropADT A → PropADT A
push-down-left a (leaf v)      (leaf v')     = leaf (a -< v >- ∷ v')
push-down-left a c@(leaf v)    (D ⟨ l , r ⟩) = D ⟨ push-down-left a c l , push-down-left a c r ⟩
push-down-left a (D ⟨ l , r ⟩) n             = D ⟨ push-down-left a l n , push-down-left a r n ⟩

-- formal specification of push-down-left: It should create an ADT such that for any configuration c, there is an artifact at the top of left
push-down-left-spec : ∀ {A} (a : atoms A) (l n : PropADT A) c
  → ⟦ push-down-left a l n ⟧ₚ c ≡ a -< ⟦ l ⟧ₚ c >- ∷ ⟦ n ⟧ₚ c
push-down-left-spec a (leaf v) (leaf v') c = refl
push-down-left-spec a (D ⟨ l , r ⟩) n c with eval D c
... | true  = push-down-left-spec a l n c
... | false = push-down-left-spec a r n c
push-down-left-spec a x@(leaf v) (D ⟨ l , r ⟩) c with eval D c
... | true  = push-down-left-spec a x l c
... | false = push-down-left-spec a x r c


mutual
  {-|
  We need this auxiliary function to prove termination.
  Given two lists l, r of neighboring variation tree nodes,
  we cannot translate them via
    translate-all (l ++ r)
  but can translate both lists first, and them compose the result
    translate-all l ⊕ translate-all r.
  -}
  translate-both : ∀ {A} → (l r : List (UnrootedVT A)) → PropADT A
  translate-both l r = translate-all l ⊕ translate-all r

  translate-all : ∀ {A} → List (UnrootedVT A) → PropADT A
  translate-all []                               = leaf []
  translate-all (a -< l >- ∷ xs)                 = push-down-left a (translate-all l) (translate-all xs)
  translate-all (if[ p ]then[ l ] ∷ xs)          = p ⟨ translate-both l xs , translate-all xs ⟩
  translate-all (if[ p ]then[ l ]else[ r ] ∷ xs) = p ⟨ translate-both l xs , translate-both r xs ⟩

translate : ∀ {A} → VT A → PropADT A
translate if-true[ xs ] = translate-all xs

-- Preservation Proofs --

preserves-all : ∀ {A} (vts : List (UnrootedVT A)) → configure-all vts ≗ ⟦ translate-all vts ⟧ₚ
preserves-all [] c = refl
preserves-all (a -< l >- ∷ xs) c =
    configure-all (a -< l >- ∷ xs) c
  ≡⟨⟩
    a -< configure-all l c >- ∷ configure-all xs c
  ≡⟨ cong (_ ∷_) (preserves-all xs c) ⟩
    a -< configure-all l c >- ∷ ⟦ translate-all xs ⟧ₚ c
  ≡⟨ cong (λ z → a -< z >- ∷ _) (preserves-all l c) ⟩
    a -< ⟦ translate-all l ⟧ₚ c >- ∷ ⟦ translate-all xs ⟧ₚ c
  ≡⟨ push-down-left-spec a (translate-all l) (translate-all xs) c ⟨
    ⟦ push-down-left a (translate-all l) (translate-all xs) ⟧ₚ c
  ∎
preserves-all (if[ p ]then[ l ] ∷ xs) c with eval p c
... | true  =
    configure-all l c ++ configure-all xs c
  ≡⟨ cong₂ _++_ (preserves-all l c) (preserves-all xs c) ⟩
    ⟦ translate-all l ⟧ₚ c ++ ⟦ translate-all xs ⟧ₚ c
  ≡⟨ ⊕-specₚ (translate-all l) (translate-all xs) c ⟨
    ⟦ translate-all l ⊕ translate-all xs ⟧ₚ c
  ≡⟨⟩
    ⟦ translate-both l xs ⟧ₚ c
  ∎
... | false = preserves-all xs c
-- The cases for the choice alternatives are analogous to the first option case above.
preserves-all (if[ p ]then[ l ]else[ r ] ∷ xs) c with eval p c
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

preserves : ∀ {A} (vt : VT A) → ⟦ vt ⟧ ≗ ⟦ translate vt ⟧ₚ
preserves if-true[ xs ] c = preserves-all xs c

VT→PropADT : LanguageCompiler VTL PropADTL
VT→PropADT = record
  { compile = translate
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = ≗→≅[] ∘ preserves
  }

PropADT≽VT : PropADTL ≽ VTL
PropADT≽VT = expressiveness-from-compiler VT→PropADT

VT→ADT : LanguageCompiler VTL ADTL
VT→ADT = VT→PropADT Compiler.⊕ formula-elim-compiler

ADT≽VT : ADTL ≽ VTL
ADT≽VT = ≽-trans ADT≽PropADT PropADT≽VT

{-|
This module contains some tests for the translation function to see it in action.
-}
module Test {A : 𝔸} where
  open Vatras.Framework.Variants using (rose-leaf; forest-leaf; forest-singleton)

  module Forest (a b : atoms A) where
    vt : VT A
    vt =
      if-true[
        vt-leaf a ∷ vt-leaf b ∷ []
      ]

    adt : PropADT A
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

    adt : PropADT A
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

    adt : PropADT A
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
