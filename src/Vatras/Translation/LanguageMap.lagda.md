# Overview of Language Relations

This module contains all our proofs for the variability languages defined so far.
In particular, this file corresponds to the map of compilers in Section 5 of our paper.

## Module

```agda
module Vatras.Translation.LanguageMap where
```

## Imports

```agda
import Data.Fin as Fin
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Size using (∞)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_; _≗_)
open import Relation.Nullary.Negation using (¬_)

open import Vatras.Framework.Variants using (Rose; Forest; Variant-is-VL)
Variant = Rose ∞

open import Vatras.Framework.Annotation.IndexedDimension
open import Vatras.Framework.Compiler
open import Vatras.Framework.Definitions using (𝕍; 𝔽)
open import Vatras.Framework.Relation.Expressiveness Variant using (_≽_; ≽-trans; _≻_; _⋡_; _≋_; compiler-cannot-exist)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Vatras.Util.AuxProofs using (decidableEquality-×)
open import Vatras.Util.String using (diagonal-ℕ; diagonal-ℕ⁻¹; diagonal-ℕ-proof)

import Vatras.Framework.Proof.ForFree
open Vatras.Framework.Proof.ForFree Variant using (less-expressive-from-completeness; completeness-by-expressiveness; soundness-by-expressiveness)
open Vatras.Framework.Proof.ForFree using () renaming (completeness-by-expressiveness to completeness-by-expressiveness-on; soundness-by-expressiveness to soundness-by-expressiveness-on)

import Vatras.Framework.Properties.Completeness
import Vatras.Framework.Properties.Soundness
open Vatras.Framework.Properties.Completeness Variant using (Complete)
open Vatras.Framework.Properties.Soundness Variant using (Sound)
open Vatras.Framework.Properties.Completeness using () renaming (Complete to Complete-on)
open Vatras.Framework.Properties.Soundness using () renaming (Sound to Sound-on)

open import Vatras.Lang.All
open VariantList using (VariantListL)
open CCC using (CCCL)
open NCC using (NCCL)
open 2CC using (2CCL)
open NADT using (NADTL)
open ADT using (ADTL)
open OC using (WFOCL)
open FST using (FSTL)
open VT using (VTL)
open PropOC using (WFPropOCL)

open import Vatras.Lang.CCC.Encode using () renaming (encoder to CCC-Rose-encoder)
open import Vatras.Translation.Lang.NCC.Rename using (NCC-rename≽NCC)
open import Vatras.Translation.Lang.2CC.Rename using (2CC-rename; 2CC-rename≽2CC)
open import Vatras.Translation.Lang.VT.Rename using (VT-rename≽VT)

import Vatras.Translation.Lang.CCC-to-NCC as CCC-to-NCC
import Vatras.Translation.Lang.NCC-to-CCC as NCC-to-CCC
import Vatras.Translation.Lang.NCC.Grow as Grow
import Vatras.Translation.Lang.NCC.ShrinkTo2 as ShrinkTo2
import Vatras.Translation.Lang.NCC.NCC-to-NCC as NCC-to-NCC
import Vatras.Translation.Lang.NCC-to-2CC as NCC-to-2CC
import Vatras.Translation.Lang.2CC-to-NCC as 2CC-to-NCC
import Vatras.Translation.Lang.Transitive.CCC-to-2CC as CCC-to-2CC
import Vatras.Translation.Lang.Transitive.2CC-to-CCC as 2CC-to-CCC
import Vatras.Translation.Lang.2CC-to-ADT as 2CC-to-ADT
import Vatras.Translation.Lang.ADT-to-2CC as ADT-to-2CC
import Vatras.Translation.Lang.ADT.DeadElim as DeadElim
import Vatras.Translation.Lang.ADT-to-VariantList as ADT-to-VariantList
import Vatras.Translation.Lang.VariantList-to-CCC as VariantList-to-CCC
import Vatras.Translation.Lang.ADT-to-NADT as ADT-to-NADT
import Vatras.Translation.Lang.NADT-to-CCC as NADT-to-CCC
import Vatras.Translation.Lang.OC-to-2CC as OC-to-2CC
import Vatras.Translation.Lang.OC-to-FST as OC-to-FST
import Vatras.Translation.Lang.FST-to-OC as FST-to-OC
import Vatras.Translation.Lang.FST-to-VariantList as FST-to-VariantList
import Vatras.Translation.Lang.VariantList-to-VT as VariantList-to-VT
import Vatras.Translation.Lang.VT-to-ADT as VT-to-ADT
import Vatras.Translation.Lang.OC-to-PropOC as OC-to-PropOC
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
open 2CC-to-ADT using (2CC→ADT) public
open ADT-to-2CC using (ADT→2CC) public

module _ {F : 𝔽} (_==_ : DecidableEquality F) where
  open DeadElim F Variant _==_ using (kill-dead-compiler) public

  open ADT-to-VariantList F Variant _==_ using (ADT→VariantList) public

module _ {F : 𝔽} (D : F) where
  open VariantList-to-CCC.Translate F D using (VariantList→CCC) public

open ADT-to-NADT using (ADT→NADT) public
NADT→CCC : ∀ {F : 𝔽} → LanguageCompiler (NADTL F Variant) (CCCL F)
NADT→CCC {F} = NADT-to-CCC.NADT→CCC CCC-Rose-encoder
```


## Option Calculus vs Binary Choice Calculus

```agda
module _ {F : 𝔽} where
  open OC-to-2CC F using (OC→2CC) public
```

## Feature Structure Trees vs Variant Lists

```agda
module _ {F : 𝔽} (_==_ : DecidableEquality F) where
  open FST-to-VariantList F _==_ using (FST→VariantList) public
```


## Expressiveness

We need to require that there exists an injection between `F × ℕ` and the
annotation language `F : 𝔽`to obtain expressiveness proofs which are independent
of the annotation language `F`. Without this restriction some expressiveness
theorems would sound like
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL (F × ℕ) n ≽ CCCL F`
whereas we would like to obtain
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL F n ≽ CCCL F`
so we can also get
  `NCC≋CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL F n ≋ CCCL F`

The intuition behind this restriction is that we may need to extend the set of
annotations `F` by new annotations. For example, when labeling the individual
choices in `NCC n` with new annotations while translating to `NCC 2` in
`Translation.Lang.NCC.ShrinkTo2`. For practical applications, expressiveness
theorems like
  `NCC≽CCC : ∀ {F : 𝔽} → (n : ℕ≥ 2) → NCCL (F × ℕ) n ≽ CCCL F`
make the changes in the feature model explicit. For theoretical results however,
it is easier to assume that the set of annotations `F` is infinite, which is
equivalent to the restriction used here (except if `F` is empty).

This assumption is reasonable because it is satisfied by natural numbers
(via [Cantor's first diagonal argument](https://de.wikipedia.org/wiki/Cantors_erstes_Diagonalargument)
which was used to show that there are countably but infinite many rational numbers)
and Strings. A witness of these preconditions for Strings can be found in `Util.String`.
An alias module for importing expressiveness fixed to Strings and with the
respective preconditions satisfied can be found below the `Expressivness` module.

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

  CCC≽NCC : ∀ (n : ℕ≥ 2) → CCCL F ≽ NCCL F n
  CCC≽NCC = NCC-to-CCC.CCC≽NCC

  NCC≽CCC : ∀ (n : ℕ≥ 2) → NCCL F n ≽ CCCL F
  NCC≽CCC n = ≽-trans (NCC-rename≽NCC n f f⁻¹ f⁻¹∘f≗id) (CCC-to-NCC.NCC≽CCC n)

  NCC≽NCC : ∀ (n m : ℕ≥ 2) → NCCL F n ≽ NCCL F m
  NCC≽NCC n m = ≽-trans (NCC-rename≽NCC n (f-Fin m) (f⁻¹-Fin m) (f⁻¹-Fin∘f-Fin≗id m)) (NCC-to-NCC.NCC≽NCC m n)

  NCC≽2CC : ∀ (n : ℕ≥ 2) → NCCL F n ≽ 2CCL F
  NCC≽2CC n = 2CC-to-NCC.NCC≽2CC n

  2CC≽NCC : ∀ (n : ℕ≥ 2) → 2CCL F ≽ NCCL F n
  2CC≽NCC n = ≽-trans (2CC-rename≽2CC (f-Fin n) (f⁻¹-Fin n) (f⁻¹-Fin∘f-Fin≗id n)) (NCC-to-2CC.2CC≽NCC n)

  CCC≽2CC : CCCL F ≽ 2CCL F
  CCC≽2CC = 2CC-to-CCC.CCC≽2CC

  2CC≽CCC : 2CCL F ≽ CCCL F
  2CC≽CCC = ≽-trans (2CC-rename≽2CC f f⁻¹ f⁻¹∘f≗id) CCC-to-2CC.2CC≽CCC

  2CC≽ADT : 2CCL F ≽ ADTL F Variant
  2CC≽ADT = ADT-to-2CC.2CC≽ADT (CCC-Rose-encoder ⊕ (CCC→2CC ⊕ 2CC-rename f f⁻¹ f⁻¹∘f≗id))

  ADT≽2CC : ADTL F Variant ≽ 2CCL F
  ADT≽2CC = 2CC-to-ADT.ADT≽2CC

  VariantList≽ADT : (_==_ : DecidableEquality F) → VariantListL Variant ≽ ADTL F Variant
  VariantList≽ADT _==_ = ADT-to-VariantList.VariantList≽ADT F Variant _==_

  VariantList≽FST : (_==_ : DecidableEquality F) → VariantListL Variant ≽ FSTL F
  VariantList≽FST _==_ = FST-to-VariantList.VariantList≽FST F _==_

  CCC≽VariantList : F → CCCL F ≽ VariantListL Variant
  CCC≽VariantList D = VariantList-to-CCC.Translate.CCC≽VariantList F D CCC-Rose-encoder

  NADT≽ADT : NADTL F Variant ≽ ADTL F Variant
  NADT≽ADT = ADT-to-NADT.NADT≽ADT Variant

  CCC≽NADT : ∀ {F : 𝔽} → CCCL F ≽ NADTL F Variant
  CCC≽NADT {F} = NADT-to-CCC.CCC≽NADT {F} CCC-Rose-encoder

  2CC≽OC : 2CCL F ≽ WFOCL F
  2CC≽OC = OC-to-2CC.2CC≽OC F

  2CC≽FST : F → (_==_ : DecidableEquality F) → 2CCL F ≽ FSTL F
  2CC≽FST D _==_ = ≽-trans 2CC≽CCC (≽-trans (CCC≽VariantList D) (VariantList≽FST _==_))


  PropOC≽OC : WFPropOCL F ≽ WFOCL F
  PropOC≽OC = OC-to-PropOC.PropOC≽OC F


  CCC≋NCC : ∀ (n : ℕ≥ 2) → CCCL F ≋ NCCL F n
  CCC≋NCC n = CCC≽NCC n , NCC≽CCC n

  NCC≋NCC : ∀ (n m : ℕ≥ 2) → NCCL F n ≋ NCCL F m
  NCC≋NCC n m = NCC≽NCC n m , NCC≽NCC m n

  NCC≋2CC : ∀ (n : ℕ≥ 2) → NCCL F n ≋ 2CCL F
  NCC≋2CC n = NCC≽2CC n , 2CC≽NCC n

  CCC≋2CC : CCCL F ≋ 2CCL F
  CCC≋2CC = CCC≽2CC , 2CC≽CCC

  2CC≋ADT : 2CCL F ≋ ADTL F Variant
  2CC≋ADT = 2CC≽ADT , ADT≽2CC

  ADT≋NADT : ADTL F Variant ≋ NADTL F Variant
  ADT≋NADT = ≽-trans ADT≽2CC (≽-trans 2CC≽CCC CCC≽NADT) , NADT≽ADT

  ADT≋VariantList : DecidableEquality F → F → ADTL F Variant ≋ VariantListL Variant
  ADT≋VariantList _==_ D = ≽-trans ADT≽2CC (≽-trans 2CC≽CCC (CCC≽VariantList D)) , VariantList≽ADT _==_

  VariantList≋CCC : DecidableEquality F → F → VariantListL Variant ≋ CCCL F
  VariantList≋CCC _==_ D = ≽-trans (VariantList≽ADT _==_) (≽-trans ADT≽2CC 2CC≽CCC) , CCC≽VariantList D
```

The following module is an alias, which you can used to import
the `Expressiveness` module above but with the set of annotations
fixed to Strings.
```agda
module Expressiveness-String = Expressiveness diagonal-ℕ diagonal-ℕ⁻¹ diagonal-ℕ-proof
```

## Completeness

```agda
module Completeness {F : 𝔽} (f : F × ℕ → F) (f⁻¹ : F → F × ℕ) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) (D : F) where
  open Expressiveness f f⁻¹ f⁻¹∘f≗id

  open import Vatras.Lang.VariantList.Properties Variant using (VariantList-is-Complete) public

  CCC-is-complete : Complete (CCCL F)
  CCC-is-complete = completeness-by-expressiveness VariantList-is-Complete (CCC≽VariantList D)

  NCC-is-complete : ∀ (n : ℕ≥ 2) → Complete (NCCL F n)
  NCC-is-complete n = completeness-by-expressiveness CCC-is-complete (NCC≽CCC n)

  2CC-is-complete : Complete (2CCL F)
  2CC-is-complete = completeness-by-expressiveness CCC-is-complete 2CC≽CCC

  ADT-is-complete : Complete (ADTL F Variant)
  ADT-is-complete = completeness-by-expressiveness 2CC-is-complete ADT≽2CC

  NADT-is-complete : Complete (NADTL F Variant)
  NADT-is-complete = completeness-by-expressiveness ADT-is-complete NADT≽ADT

  open import Vatras.Lang.OC.IncompleteOnRose using (OC-is-incomplete)

  OC⋡2CC : WFOCL F ⋡ 2CCL F
  OC⋡2CC = less-expressive-from-completeness 2CC-is-complete OC-is-incomplete

  2CC≻WFOC : 2CCL F ≻ WFOCL F
  2CC≻WFOC = 2CC≽OC , OC⋡2CC

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler (2CCL F) (WFOCL F))
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC⋡2CC

  open import Vatras.Lang.FST.IncompleteOnRose using (FST-is-incomplete)

  FST⋡2CC : FSTL F ⋡ 2CCL F
  FST⋡2CC = less-expressive-from-completeness 2CC-is-complete FST-is-incomplete

  FST⋡VariantList : FSTL F ⋡ VariantListL Variant
  FST⋡VariantList = less-expressive-from-completeness VariantList-is-Complete FST-is-incomplete

  2CC-cannot-be-compiled-to-FST : ¬ (LanguageCompiler (2CCL F) (FSTL F))
  2CC-cannot-be-compiled-to-FST = compiler-cannot-exist FST⋡2CC

  open OC-to-FST using (FST⋡WFOC)

  FST⋡OC : FSTL F ⋡ WFOCL F
  FST⋡OC = FST⋡WFOC F

  OC-cannot-be-compiled-to-FST : ¬ (LanguageCompiler (WFOCL F) (FSTL F))
  OC-cannot-be-compiled-to-FST = compiler-cannot-exist FST⋡OC
```

For the proof of `WFOCL⋡FSTL`, we need to construct at least three distinct
configurations. Hence, we need at least two distint features and a method for
comparing these features to decided which values these features are assigned.
```agda
  module _ {F' : 𝔽} (f₁ f₂ : F') (f₁≢f₂ : f₁ ≢ f₂) (_==ꟳ_ : DecidableEquality F') where
    open FST-to-OC f₁ f₂ f₁≢f₂ _==ꟳ_ using (WFOC⋡FST)

    OC-is-less-expressive-than-FST : WFOCL F ⋡ FSTL F'
    OC-is-less-expressive-than-FST = WFOC⋡FST {F}

    FST-cannot-be-compiled-to-OC : ¬ LanguageCompiler (FSTL F') (WFOCL F)
    FST-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-FST
```

As for `Expressiveness` we re-export `Completeness` fixed to String and its respective proofs.
```agda
module Completeness-String = Completeness diagonal-ℕ diagonal-ℕ⁻¹ diagonal-ℕ-proof
```

```agda
open import Vatras.Lang.VariantList.Properties Variant using (VariantList-is-Sound) public

ADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (ADTL F Variant)
ADT-is-sound {F} _==_ = soundness-by-expressiveness VariantList-is-Sound (ADT-to-VariantList.VariantList≽ADT F Variant _==_)

2CC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (2CCL F)
2CC-is-sound _==_ = soundness-by-expressiveness (ADT-is-sound _==_) 2CC-to-ADT.ADT≽2CC

NCC-is-sound : ∀ {F : 𝔽} (n : ℕ≥ 2) (_==_ : DecidableEquality F) → Sound (NCCL F n)
NCC-is-sound n _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ Fin._≟_)) (NCC-to-2CC.2CC≽NCC n)

CCC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (CCCL F)
CCC-is-sound _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ ℕ._≟_)) CCC-to-2CC.2CC≽CCC

NADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (NADTL F Variant)
NADT-is-sound _==_ = soundness-by-expressiveness (CCC-is-sound _==_) (NADT-to-CCC.CCC≽NADT CCC-Rose-encoder)

OC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (WFOCL F)
OC-is-sound {F} _==_ = soundness-by-expressiveness (2CC-is-sound _==_) (OC-to-2CC.2CC≽OC F)

FST-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (FSTL F)
FST-is-sound {F} _==_ = soundness-by-expressiveness VariantList-is-Sound (FST-to-VariantList.VariantList≽FST F _==_)
```

Variation Trees assume variants to be forests of rose trees.
We hence cannot directly integrate it into the circle of compilers above.
Yet, variant lists and ADTs are generic in their type of variants and hence can also denote forests.
```agda
open import Vatras.Lang.VariantList.Properties
  using ()
  renaming (VariantList-is-Sound to VariantList-is-sound-on; VariantList-is-Complete to VariantList-is-complete-on)

ADT-is-sound-on : ∀ {F : 𝔽} (V : 𝕍) (_==_ : DecidableEquality F) → Sound-on V (ADTL F V)
ADT-is-sound-on {F} V _==_ = soundness-by-expressiveness-on V (VariantList-is-sound-on V) (ADT-to-VariantList.VariantList≽ADT F V _==_)

VTℕ-is-complete : Complete-on Forest (VTL ℕ)
VTℕ-is-complete = VariantList-to-VT.VT-is-complete

VT-is-complete : {F : 𝔽} (f : ℕ → F) (f⁻¹ : F → ℕ) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id)
  → Complete-on Forest (VTL F)
VT-is-complete f f⁻¹ f⁻¹∘f≗id = completeness-by-expressiveness-on Forest VTℕ-is-complete (VT-rename≽VT f f⁻¹ f⁻¹∘f≗id)

VT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound-on Forest (VTL F)
VT-is-sound {F} _==_ = soundness-by-expressiveness-on Forest (ADT-is-sound-on Forest _==_) (VT-to-ADT.ADT≽VT F)
```
