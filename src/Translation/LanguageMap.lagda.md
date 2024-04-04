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
```


## Core Choice Calculus vs Binary Choice Calculus

```agda
open import Translation.Lang.CCC-to-NCC Variant mkArtifact using (CCC→NCC; NCC≽CCC) public
open import Translation.Lang.NCC-to-CCC Variant mkArtifact using (NCC→CCC; CCC≽NCC) public

open import Translation.Lang.NCC.Grow Variant mkArtifact using (growCompiler) public
open import Translation.Lang.NCC.ShrinkTo2 Variant mkArtifact using (shrinkTo2Compiler) public
-- Generalization of the grow and shrink
open import Translation.Lang.NCC.NCC-to-NCC Variant mkArtifact using (NCC→NCC; NCC≽NCC) public

open import Translation.Lang.NCC-to-2CC Variant mkArtifact using (NCC→2CC; 2CC≽NCC) public
open import Translation.Lang.2CC-to-NCC Variant mkArtifact using (2CC→NCC; NCC≽2CC) public

open import Translation.Lang.Transitive.CCC-to-2CC Variant mkArtifact using (CCC→2CC; 2CC≽CCC) public
open import Translation.Lang.Transitive.2CC-to-CCC Variant mkArtifact using (2CC→CCC; CCC≽2CC) public
```

```agda
open import Translation.Lang.2CC-to-2ADT Variant mkArtifact using (2CC→2ADT; 2ADT≽2CC) public
-- open import Translation.Lang.2ADT-to-2CC Variant mkArtifact using () public

module _ {F : 𝔽} (_==_ : DecidableEquality F) where
  open import Translation.Lang.2ADT.DeadElim F Variant _==_ using (kill-dead-compiler) public

  open import Translation.Lang.2ADT-to-VariantList F Variant _==_ using (2ADT→VariantList; VariantList≽2ADT) public

import Translation.Lang.VariantList-to-CCC
module _ {F : 𝔽} (D : F) where
  open Translation.Lang.VariantList-to-CCC.Translate F D Variant mkArtifact CCC-Rose-encoder using (VariantList→CCC; CCC≽VariantList) public

open import Translation.Lang.2ADT-to-NADT Variant mkArtifact using (2ADT→NADT; NADT≽2ADT) public
open import Translation.Lang.NADT-to-CCC Variant mkArtifact using (NADT→CCC) public
module _ {F : 𝔽} where
  open import Translation.Lang.NADT-to-CCC Variant mkArtifact using () renaming (CCC≽NADT to CCC≽NADT')
  CCC≽NADT = CCC≽NADT' {F} CCC-Rose-encoder
```

## Option Calculus vs Binary Choice Calculus
```agda
module _ {F : 𝔽} where
  open import Translation.Lang.OC-to-2CC F using (OC→2CC; 2CC≽OC) public
```

```agda
module _ {F : 𝔽} (f : F × ℕ → F) (f⁻¹ : F → F × ℕ) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) where
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

  CCC≋NCC : ∀ (n : ℕ≥ 2) → CCCL F ≋ NCCL n F
  CCC≋NCC n = CCC≽NCC n , ≽-trans (NCC-rename≽NCC n f f⁻¹ f⁻¹∘f≗id) (NCC≽CCC n)

  NCC≋NCC : ∀ (n m : ℕ≥ 2) → NCCL n F ≋ NCCL m F
  NCC≋NCC n m = ≽-trans (NCC-rename≽NCC n (f-Fin m) (f⁻¹-Fin m) (f⁻¹-Fin∘f-Fin≗id m)) (NCC≽NCC m n) , ≽-trans (NCC-rename≽NCC m (f-Fin n) (f⁻¹-Fin n) (f⁻¹-Fin∘f-Fin≗id n)) (NCC≽NCC n m)

  NCC≋2CC : ∀ (n : ℕ≥ 2) → NCCL n F ≋ 2CCL F
  NCC≋2CC n = NCC≽2CC n , ≽-trans (2CC-rename≽2CC (f-Fin n) (f⁻¹-Fin n) (f⁻¹-Fin∘f-Fin≗id n)) (2CC≽NCC n)

  CCC≋2CC : CCCL F ≋ 2CCL F
  CCC≋2CC = CCC≽2CC , ≽-trans (2CC-rename≽2CC f f⁻¹ f⁻¹∘f≗id) 2CC≽CCC

  2CC≋2ADT : 2CCL F ≋ 2ADTL Variant F
  2CC≋2ADT = {!2CC≽2ADT!} , 2ADT≽2CC

  2ADT≋NADT : 2ADTL Variant (F × ℕ) ≋ NADTL Variant F
  2ADT≋NADT = ≽-trans 2ADT≽2CC (≽-trans 2CC≽CCC CCC≽NADT) , ≽-trans NADT≽2ADT {!2ADT-rename≽2ADT!}

  2ADT≋VariantList : DecidableEquality F → F → 2ADTL Variant (F × ℕ) ≋ VariantListL
  2ADT≋VariantList _==_ D = ≽-trans 2ADT≽2CC (≽-trans 2CC≽CCC (CCC≽VariantList D)) , VariantList≽2ADT (decidableEquality-× _==_ ℕ._≟_)

  VariantList≋CCC : DecidableEquality F → (F × ℕ) → VariantListL ≋ CCCL (F × ℕ)
  VariantList≋CCC _==_ D = ≽-trans (VariantList≽2ADT (decidableEquality-× (decidableEquality-× _==_ ℕ._≟_) ℕ._≟_)) (≽-trans 2ADT≽2CC 2CC≽CCC) , CCC≽VariantList D
```

```agda
module _ {F : 𝔽} (D : F) where
  CCC-is-complete : Complete (CCCL F)
  CCC-is-complete = completeness-by-expressiveness VariantList-is-Complete (CCC≽VariantList D)

  NCC-is-complete : ∀ (n : ℕ≥ 2) → Complete (NCCL n (F × ℕ))
  NCC-is-complete n = completeness-by-expressiveness CCC-is-complete (NCC≽CCC n)

  2CC-is-complete : Complete (2CCL (F × ℕ))
  2CC-is-complete = completeness-by-expressiveness CCC-is-complete 2CC≽CCC

  2ADT-is-complete : Complete (2ADTL Variant (F × ℕ))
  2ADT-is-complete = completeness-by-expressiveness 2CC-is-complete 2ADT≽2CC

  NADT-is-complete : Complete (NADTL Variant (F × ℕ))
  NADT-is-complete = completeness-by-expressiveness 2ADT-is-complete NADT≽2ADT

  open OC.IncompleteOnRose using (OC-is-incomplete)

  OC-is-less-expressive-than-2CC : WFOCL F ⋡ 2CCL (F × ℕ)
  OC-is-less-expressive-than-2CC = less-expressive-from-completeness 2CC-is-complete OC-is-incomplete

  2CC-cannot-be-compiled-to-OC : ¬ (LanguageCompiler (2CCL (F × ℕ)) (WFOCL F))
  2CC-cannot-be-compiled-to-OC = compiler-cannot-exist OC-is-less-expressive-than-2CC
```

```agda
2ADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (2ADTL Variant F)
2ADT-is-sound _==_ = soundness-by-expressiveness VariantList-is-Sound (VariantList≽2ADT _==_)

2CC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (2CCL F)
2CC-is-sound _==_ = soundness-by-expressiveness (2ADT-is-sound _==_) 2ADT≽2CC

NCC-is-sound : ∀ {F : 𝔽} (n : ℕ≥ 2) (_==_ : DecidableEquality F) → Sound (NCCL n F)
NCC-is-sound n _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ Fin._≟_)) (2CC≽NCC n)

CCC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (CCCL F)
CCC-is-sound _==_ = soundness-by-expressiveness (2CC-is-sound (decidableEquality-× _==_ ℕ._≟_)) 2CC≽CCC

NADT-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (NADTL Variant F)
NADT-is-sound _==_ = soundness-by-expressiveness (CCC-is-sound _==_) CCC≽NADT

OC-is-sound : ∀ {F : 𝔽} (_==_ : DecidableEquality F) → Sound (WFOCL F)
OC-is-sound _==_ = soundness-by-expressiveness (2CC-is-sound _==_) 2CC≽OC
```
