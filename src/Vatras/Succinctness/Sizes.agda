open import Vatras.Framework.Definitions using (𝔽; 𝕍; 𝔸; atoms; atomSize)
module Vatras.Succinctness.Sizes where

open import Data.Nat using (ℕ; suc; zero; _+_; _>_; s≤s; z≤n)
import Data.List as List
import Data.List.NonEmpty as List⁺
import Data.Vec as Vec
open import Function using (_∘_)
open import Size using (Size; ∞)

open import Vatras.Data.Prop using (Prop; true; false; var; ¬_; _∧_)
open import Vatras.Util.Nat.AtLeast using (ℕ≥)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; Expression)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All

record SizedLang (V : 𝕍) : Set₂ where
  field
    Lang : VariabilityLanguage V
    size : {A : 𝔸} → Expression Lang A → ℕ
open SizedLang public

sizeRose : ∀ {i : Size} {A : 𝔸} → Rose i A → ℕ
sizeRose {A = A} (a Rose.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeRose cs))

sizeRose>0 : ∀ {i : Size} {A : 𝔸} → (v : Rose i A) → sizeRose v > 0
sizeRose>0 {A = A} (a Rose.-< cs >-) = s≤s z≤n

size2CC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → 2CC.2CC F i A → ℕ
size2CC {A = A} (a 2CC.2CC.-< cs >-) = suc (atomSize A a + List.sum (List.map size2CC cs))
size2CC (D 2CC.2CC.⟨ l , r ⟩) = suc (size2CC l + size2CC r)

size2CC>0 : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → (2cc : 2CC.2CC F i A) → size2CC 2cc > 0
size2CC>0 (a 2CC.-< cs >-) = s≤s z≤n
size2CC>0 (D 2CC.⟨ l , r ⟩) = s≤s z≤n

Sized2CC : 𝔽 → SizedLang (Rose ∞)
Sized2CC F = record
  { Lang = 2CC.2CCL F
  ; size = size2CC
  }

sizeNCC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} (n : ℕ≥ 2) → NCC.NCC F n i A → ℕ
sizeNCC {A = A} n (a NCC.NCC.-< cs >-) = suc (atomSize A a + List.sum (List.map (sizeNCC n) cs))
sizeNCC n (D NCC.NCC.⟨ cs ⟩) = suc (Vec.sum (Vec.map (sizeNCC n) cs))

SizedNCC : 𝔽 → ℕ≥ 2 → SizedLang (Rose ∞)
SizedNCC F n = record
  { Lang = NCC.NCCL F n
  ; size = sizeNCC n
  }

sizeCCC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → CCC.CCC F i A → ℕ
sizeCCC {A = A} (a CCC.CCC.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeCCC cs))
sizeCCC (D CCC.CCC.⟨ cs ⟩) = suc (List.sum (List.map sizeCCC (List⁺.toList cs)))

sizeCCC>0 : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → (ccc : CCC.CCC F i A) → sizeCCC ccc > 0
sizeCCC>0 (a CCC.-< cs >-) = s≤s z≤n
sizeCCC>0 (D CCC.⟨ cs ⟩) = s≤s z≤n

SizedCCC : 𝔽 → SizedLang (Rose ∞)
SizedCCC F = record
  { Lang = CCC.CCCL F
  ; size = sizeCCC
  }

sizeADT : {F : 𝔽} {V : 𝕍} {A : 𝔸} → ({A : 𝔸} → V A → ℕ) → ADT.ADT F V A → ℕ
sizeADT variantSize (ADT.ADT.leaf v) = suc (variantSize v)
sizeADT variantSize (D ADT.ADT.⟨ l , r ⟩) = suc (sizeADT variantSize l + sizeADT variantSize r)

sizeADT>0 : {F : 𝔽} {V : 𝕍} → (variantSize : {A : 𝔸} → V A → ℕ) → {A : 𝔸} → (adt : ADT.ADT F V A) → sizeADT variantSize adt > 0
sizeADT>0 variantSize (ADT.ADT.leaf v) = s≤s z≤n
sizeADT>0 variantSize (D ADT.ADT.⟨ l , r ⟩) = s≤s z≤n

SizedADT : 𝔽 → (V : 𝕍) → ({A : 𝔸} → V A → ℕ) → SizedLang V
SizedADT F V variantSize = record
  { Lang = ADT.ADTL F V
  ; size = sizeADT variantSize
  }

sizeNADT : {F : 𝔽} {V : 𝕍} {i : Size} {A : 𝔸} → ({A : 𝔸} → V A → ℕ) → NADT.NADT F V i A → ℕ
sizeNADT variantSize (NADT.NADT.leaf v) = suc (variantSize v)
sizeNADT variantSize (D NADT.NADT.⟨ cs ⟩) = suc (List.sum (List.map (sizeNADT variantSize) (List⁺.toList cs)))

sizeNADT>0 : {F : 𝔽} {V : 𝕍} → (variantSize : {A : 𝔸} → V A → ℕ) → {A : 𝔸} → {i : Size} → (nadt : NADT.NADT F V i A) → sizeNADT variantSize nadt > 0
sizeNADT>0 variantSize (NADT.NADT.leaf v) = s≤s z≤n
sizeNADT>0 variantSize (D NADT.NADT.⟨ cs ⟩) = s≤s z≤n

SizedNADT : 𝔽 → (V : 𝕍) → ({A : 𝔸} → V A → ℕ) → SizedLang V
SizedNADT F V variantSize = record
  { Lang = NADT.NADTL F V
  ; size = sizeNADT variantSize
  }

sizeVariantList : {V : 𝕍} {A : 𝔸} → ({A : 𝔸} → V A → ℕ) → VariantList.VariantList V A → ℕ
sizeVariantList variantSize l = List.sum (List.map variantSize (List⁺.toList l))

SizedVariantList : (V : 𝕍) → ({A : 𝔸} → V A → ℕ) → SizedLang V
SizedVariantList V variantSize = record
  { Lang = VariantList.VariantListL V
  ; size = sizeVariantList {V = V} variantSize
  }

sizeOC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → OC.OC F i A → ℕ
sizeOC {A = A} (a OC.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeOC cs))
sizeOC (D OC.❲ c ❳) = suc (sizeOC c)

sizeOC>0 : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → (oc : OC.OC F i A) → sizeOC oc > 0
sizeOC>0 (a OC.-< cs >-) = s≤s z≤n
sizeOC>0 (f OC.❲ c ❳) = s≤s z≤n

sizeWFOC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → OC.WFOC F i A → ℕ
sizeWFOC {A = A} (OC.Root a cs) = suc (atomSize A a + List.sum (List.map sizeOC cs))

SizedWFOC : 𝔽 → SizedLang (Rose ∞)
SizedWFOC F = record
  { Lang = OC.WFOCL F
  ; size = sizeWFOC
  }

sizeFST : {F : 𝔽} {A : 𝔸} → FST.Impose.SPL {F} A → ℕ
sizeFST (root FST.Impose.◀ features) = 1 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) features)

SizedFST : 𝔽 → SizedLang (Rose ∞)
SizedFST F = record
  { Lang = FST.FSTL F
  ; size = sizeFST
  }


sizeProp : ∀ {F : 𝔽} → Prop F → ℕ
sizeProp true = 1
sizeProp false = 1
sizeProp (var v) = 1
sizeProp (¬ e) = suc (sizeProp e)
sizeProp (e₁ ∧ e₂) = suc (sizeProp e₁ + sizeProp e₂)

sizePropOC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → PropOC.PropOC F i A → ℕ
sizePropOC {A = A} (a PropOC.-< cs >-) = suc (atomSize A a + List.sum (List.map sizePropOC cs))
sizePropOC (prop PropOC.❲ c ❳) = suc (sizeProp prop + sizePropOC c)

sizeWFPropOC : ∀ {F : 𝔽} {i : Size} {A : 𝔸} → PropOC.WFPropOC F i A → ℕ
sizeWFPropOC {A = A} (PropOC.Root a cs) = suc (atomSize A a + List.sum (List.map sizePropOC cs))

SizedWFPropOC : 𝔽 → SizedLang (Rose ∞)
SizedWFPropOC F = record
  { Lang = PropOC.WFPropOCL F
  ; size = sizeWFPropOC
  }
