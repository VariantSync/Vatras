# Overview of Language Relations

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.LanguageMap where
```

## Imports

```agda
import Data.Fin as Fin
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Size using (∞)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Variants using (Rose; Artifact∈ₛRose; Variant-is-VL)
Variant = Rose ∞
mkArtifact = Artifact∈ₛRose

open import Framework.Annotation.IndexedDimension
open import Framework.Construct
open import Framework.Compiler
open import Framework.Definitions using (𝕍; 𝔽)
open import Framework.Relation.Expressiveness Variant using (_≽_; ≽-trans; _⋡_; _≋_; compiler-cannot-exist)
open import Framework.Proof.Transitive Variant using (less-expressive-from-completeness; completeness-by-expressiveness; soundness-by-expressiveness)
open import Framework.Properties.Completeness Variant using (Complete)
open import Framework.Properties.Soundness Variant using (Sound)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Util.AuxProofs using (decidableEquality-×)

open import Construct.Artifact as At using () renaming (Syntax to Artifact)

open import Lang.All
open VariantList using (VariantListL; VariantList-is-Complete; VariantList-is-Sound)
open CCC using (CCCL)
open NCC using (NCCL)
open 2CC using (2CCL)
open NADT using (NADTL)
open 2ADT using (2ADTL)
open OC using (WFOCL)

open CCC.Encode using () renaming (encoder to CCC-Rose-encoder)
open import Translation.Lang.NCC.Rename Variant mkArtifact using (NCC-rename≽NCC)
open import Translation.Lang.2CC.Rename Variant mkArtifact using (2CC-rename; 2CC-rename≽2CC)

import Translation.Lang.CCC-to-NCC Variant mkArtifact as CCC-to-NCC
import Translation.Lang.NCC-to-CCC Variant mkArtifact as NCC-to-CCC
import Translation.Lang.NCC.Grow Variant mkArtifact as Grow
import Translation.Lang.NCC.ShrinkTo2 Variant mkArtifact as ShrinkTo2
import Translation.Lang.NCC.NCC-to-NCC Variant mkArtifact as NCC-to-NCC
import Translation.Lang.NCC-to-2CC Variant mkArtifact as NCC-to-2CC
import Translation.Lang.2CC-to-NCC Variant mkArtifact as 2CC-to-NCC
import Translation.Lang.Transitive.CCC-to-2CC Variant mkArtifact as CCC-to-2CC
import Translation.Lang.Transitive.2CC-to-CCC Variant mkArtifact as 2CC-to-CCC
import Translation.Lang.2CC-to-2ADT Variant mkArtifact as 2CC-to-2ADT
import Translation.Lang.2ADT-to-2CC Variant mkArtifact as 2ADT-to-2CC
import Translation.Lang.2ADT.DeadElim as DeadElim
import Translation.Lang.2ADT-to-VariantList as 2ADT-to-VariantList
import Translation.Lang.VariantList-to-CCC as VariantList-to-CCC
import Translation.Lang.2ADT-to-NADT Variant mkArtifact as 2ADT-to-NADT
import Translation.Lang.NADT-to-CCC Variant mkArtifact as NADT-to-CCC
import Translation.Lang.OC-to-2CC as OC-to-2CC
```


## Core Choice Calculus vs Binary Choice Calculus

```agda
open CCC-to-NCC using (CCC→NCC) public
open NCC-to-CCC using (NCC→CCC) public

open Grow using (growCompiler) public
open ShrinkTo2 using (shrinkTo2Compiler) public
-- Generalization of grow and shrink
open NCC-to-NCC using (NCC→NCC) public

open NCC-to-2CC using (NCC→2CC) public
open 2CC-to-NCC using (2CC→NCC) public

open CCC-to-2CC using (CCC→2CC) public
open 2CC-to-CCC using (2CC→CCC) public
```


## Choices vs Algebraic Decision Trees

```agda
open 2CC-to-2ADT using (2CC→2ADT) public
open 2ADT-to-2CC using (2ADT→2CC) public

module _ {F : 𝔽} (_==_ : DecidableEquality F) where
  open DeadElim F Variant _==_ using (kill-dead-compiler) public

  open 2ADT-to-VariantList F Variant _==_ using (2ADT→VariantList) public

module _ {F : 𝔽} (D : F) where
  open VariantList-to-CCC.Translate F D Variant mkArtifact CCC-Rose-encoder using (VariantList→CCC) public

open 2ADT-to-NADT using (2ADT→NADT) public
NADT→CCC : ∀ {F : 𝔽} → LanguageCompiler (NADTL Variant F) (CCCL F)
NADT→CCC {F} = NADT-to-CCC.NADT→CCC {F = F} CCC-Rose-encoder
```


## Option Calculus vs Binary Choice Calculus

```agda
module _ {F : 𝔽} where
  open OC-to-2CC F using (OC→2CC) public
```


## Expressiveness

We need to require that there exists an injection between `F × ℕ` and the
annotation language `F : 𝔽`to obtain expressiveness proofs which are independent
of the annotation language `F`. Without this restriction some expressiveness
theorems would sound like
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL n (F × ℕ) ≽ CCCL F`
whereas we would like to obtain
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL n F ≽ CCCL F`
so we can also get
  `NCC≋CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL n F ≋ CCCL F`

The intuition behind this restriction is that we may need to extend the set of
annotations `F` by new annotations. For example, when labeling the individual
choices in `NCC n` with new annotations while translating to `NCC 2` in
`Translation.Lang.NCC.ShrinkTo2`. For practical applications, expressiveness
theorems like
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL n (F × ℕ) ≽ CCCL F`
make the changes in the feature model explicit. For theoretical results however,
it is easier to assume that the set of annotations `F` is infinite, which is
equivalent to the restriction used here (except if `F` is empty).

A witness of these preconditions can be faund in `Util.String`.

```agda
module Expressiveness {F : 𝔽} (f : F × ℕ → F) (f⁻¹ : F → F × ℕ) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) where
  private
    f-Fin : ∀ (n : ℕ≥ 2) → IndexedDimension F n → F
    f-Fin n (D , k) = f (D , Fin.toℕ k)

    f⁻¹-Fin : ∀ (n : ℕ≥ 2) → F → IndexedDimension F n
    f⁻¹-Fin (sucs n) D with f⁻¹ D
    ... | D' , k = D' , ℕ≥.cappedFin k

    f⁻¹-Fin∘f-Fin≗id : ∀ (n : ℕ≥ 2) → f⁻¹-Fin n ∘ f-Fin n ≗ id
    f⁻¹-Fin∘f-Fin≗id (sucs n) (D , k) = Eq.cong₂ _,_
      (Eq.cong proj₁ (f⁻¹∘f≗id (D , Fin.toℕ k)))
      (Eq.trans (Eq.cong (ℕ≥.cappedFin ∘ proj₂) (f⁻¹∘f≗id (D , Fin.toℕ k))) (ℕ≥.cappedFin-toℕ k))

  CCC≽NCC : ∀ (n : ℕ≥ 2) → CCCL F ≽ NCCL n F
  CCC≽NCC = NCC-to-CCC.CCC≽NCC

  NCC≽CCC : ∀ (n : ℕ≥ 2) → NCCL n F ≽ CCCL F
  NCC≽CCC n = ≽-trans (NCC-rename≽NCC n f f⁻¹ f⁻¹∘f≗id) (CCC-to-NCC.NCC≽CCC n)

  NCC≽NCC : ∀ (n m : ℕ≥ 2) → NCCL n F ≽ NCCL m F
  NCC≽NCC n m = ≽-trans (NCC-rename≽NCC n (f-Fin m) (f⁻¹-Fin m) (f⁻¹-Fin∘f-Fin≗id m)) (NCC-to-NCC.NCC≽NCC m n)

  NCC≽2CC : ∀ (n : ℕ≥ 2) → NCCL n F ≽ 2CCL F
  NCC≽2CC n = 2CC-to-NCC.NCC≽2CC n

  2CC≽NCC : ∀ (n : ℕ≥ 2) → 2CCL F ≽ NCCL n F
  2CC≽NCC n = ≽-trans (2CC-rename≽2CC (f-Fin n) (f⁻¹-Fin n) (f⁻¹-Fin∘f-Fin≗id n)) (NCC-to-2CC.2CC≽NCC n)

  CCC≽2CC : CCCL F ≽ 2CCL F
  CCC≽2CC = 2CC-to-CCC.CCC≽2CC

  2CC≽CCC : 2CCL F ≽ CCCL F
  2CC≽CCC = ≽-trans (2CC-rename≽2CC f f⁻¹ f⁻¹∘f≗id) CCC-to-2CC.2CC≽CCC

  2CC≽2ADT : 2CCL F ≽ 2ADTL Variant F
  2CC≽2ADT = 2ADT-to-2CC.2CC≽2ADT (CCC-Rose-encoder ⊕ (CCC→2CC ⊕ 2CC-rename f f⁻¹ f⁻¹∘f≗id))

  2ADT≽2CC : 2ADTL Variant F ≽ 2CCL F
  2ADT≽2CC = 2CC-to-2ADT.2ADT≽2CC

  VariantList≽2ADT : (_==_ : DecidableEquality F) → VariantListL ≽ 2ADTL Variant F
  VariantList≽2ADT _==_ = 2ADT-to-VariantList.VariantList≽2ADT F Variant _==_

  CCC≽VariantList : F → CCCL F ≽ VariantListL
  CCC≽VariantList D = VariantList-to-CCC.Translate.CCC≽VariantList F D Variant mkArtifact CCC-Rose-encoder

  NADT≽2ADT : NADTL Variant F ≽ 2ADTL Variant F
  NADT≽2ADT = 2ADT-to-NADT.NADT≽2ADT

  CCC≽NADT : ∀ {F : 𝔽} → CCCL F ≽ NADTL Variant F
  CCC≽NADT {F} = NADT-to-CCC.CCC≽NADT {F} CCC-Rose-encoder

  2CC≽OC : 2CCL F ≽ WFOCL F
  2CC≽OC = OC-to-2CC.2CC≽OC F


  CCC≋NCC : ∀ (n : ℕ≥ 2) → CCCL F ≋ NCCL n F
  CCC≋NCC n = CCC≽NCC n , NCC≽CCC n

  NCC≋NCC : ∀ (n m : ℕ≥ 2) → NCCL n F ≋ NCCL m F
  NCC≋NCC n m = NCC≽NCC n m , NCC≽NCC m n

  NCC≋2CC : ∀ (n : ℕ≥ 2) → NCCL n F ≋ 2CCL F
  NCC≋2CC n = NCC≽2CC n , 2CC≽NCC n

  CCC≋2CC : CCCL F ≋ 2CCL F
  CCC≋2CC = CCC≽2CC , 2CC≽CCC

  2CC≋2ADT : 2CCL F ≋ 2ADTL Variant F
  2CC≋2ADT = 2CC≽2ADT , 2ADT≽2CC

  2ADT≋NADT : 2ADTL Variant F ≋ NADTL Variant F
  2ADT≋NADT = ≽-trans 2ADT≽2CC (≽-trans 2CC≽CCC CCC≽NADT) , NADT≽2ADT

  2ADT≋VariantList : DecidableEquality F → F → 2ADTL Variant F ≋ VariantListL
  2ADT≋VariantList _==_ D = ≽-trans 2ADT≽2CC (≽-trans 2CC≽CCC (CCC≽VariantList D)) , VariantList≽2ADT _==_

  VariantList≋CCC : DecidableEquality F → F → VariantListL ≋ CCCL F
  VariantList≋CCC _==_ D = ≽-trans (VariantList≽2ADT _==_) (≽-trans 2ADT≽2CC 2CC≽CCC) , CCC≽VariantList D
```


## Completeness

```agda
module Completeness {F : 𝔽} (f : F × ℕ → F) (f⁻¹ : F → F × ℕ) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) (D : F) where
  open Expressiveness f f⁻¹ f⁻¹∘f≗id

  CCC-is-complete : Complete (CCCL F)
  CCC-is-complete = completeness-by-expressiveness VariantList-is-Complete (CCC≽VariantList D)

  NCC-is-complete : ∀ (n : ℕ≥ 2) → Complete (NCCL n F)
  NCC-is-complete n = completeness-by-expressiveness CCC-is-complete (NCC≽CCC n)

  2CC-is-complete : Complete (2CCL F)
  2CC-is-complete = completeness-by-expressiveness CCC-is-complete 2CC≽CCC

  2ADT-is-complete : Complete (2ADTL Variant F)
  2ADT-is-complete = completeness-by-expressiveness 2CC-is-complete 2ADT≽2CC

  NADT-is-complete : Complete (NADTL Variant F)
  NADT-is-complete = completeness-by-expressiveness 2ADT-is-complete NADT≽2ADT

  open OC.IncompleteOnRose using (OC-is-incomplete)

  OC-is-less-expressive-than-2CC : WFOCL F ⋡ 2CCL F
  OC-is-less-expressive-than-2CC = less-expressive-from-completeness 2CC-is-complete OC-is-incomplete

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler (2CCL F) (WFOCL F))
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-2CC
```

```agda
2ADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (2ADTL Variant F)
2ADT-is-sound {F} _==_ = soundness-by-expressiveness VariantList-is-Sound (2ADT-to-VariantList.VariantList≽2ADT F Variant _==_)

2CC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (2CCL F)
2CC-is-sound _==_ = soundness-by-expressiveness (2ADT-is-sound _==_) 2CC-to-2ADT.2ADT≽2CC

NCC-is-sound : ∀ {F : 𝔽} (n : ℕ≥ 2) (_==_ : DecidableEquality F) → Sound (NCCL n F)
NCC-is-sound n _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ Fin._≟_)) (NCC-to-2CC.2CC≽NCC n)

CCC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (CCCL F)
CCC-is-sound _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ ℕ._≟_)) CCC-to-2CC.2CC≽CCC

NADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (NADTL Variant F)
NADT-is-sound _==_ = soundness-by-expressiveness (CCC-is-sound _==_) (NADT-to-CCC.CCC≽NADT CCC-Rose-encoder)

OC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (WFOCL F)
OC-is-sound {F} _==_ = soundness-by-expressiveness (2CC-is-sound _==_) (OC-to-2CC.2CC≽OC F)
```
