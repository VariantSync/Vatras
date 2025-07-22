open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; atomSize)
module Vatras.SyntacticExpressiveness.Sizes (F : 𝔽) where

open import Data.Nat using (ℕ; suc; zero; _+_; _>_; s≤s; z≤n)
import Data.List as List
import Data.List.NonEmpty as List⁺
import Data.Vec as Vec
open import Function using (_∘_)
open import Size using (Size; ∞)

open import Vatras.Util.Nat.AtLeast using (ℕ≥)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.SyntacticExpressiveness using (SizedLang)

sizeRose : ∀ {i : Size} {A : 𝔸} → Rose i A → ℕ
sizeRose {A = A} (a Rose.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeRose cs))

size2CC : ∀ {i : Size} {A : 𝔸} → 2CC.2CC i A → ℕ
size2CC {A = A} (a 2CC.2CC.-< cs >-) = suc (atomSize A a + List.sum (List.map size2CC cs))
size2CC (D 2CC.2CC.⟨ l , r ⟩) = suc (size2CC l + size2CC r)

size2CC>0 : ∀ {i : Size} {A : 𝔸} → (2cc : 2CC.2CC i A) → size2CC 2cc > 0
size2CC>0 (a 2CC.-< cs >-) = s≤s z≤n
size2CC>0 (D 2CC.⟨ l , r ⟩) = s≤s z≤n

Sized2CC : SizedLang
Sized2CC = record
  { Lang = 2CC.2CCL
  ; size = size2CC
  }

sizeNCC : ∀ {i : Size} {A : 𝔸} (n : ℕ≥ 2) → NCC.NCC n i A → ℕ
sizeNCC {A = A} n (a NCC.NCC.-< cs >-) = suc (atomSize A a + List.sum (List.map (sizeNCC n) cs))
sizeNCC n (D NCC.NCC.⟨ cs ⟩) = suc (Vec.sum (Vec.map (sizeNCC n) cs))

SizedNCC : ℕ≥ 2 → SizedLang
SizedNCC n = record
  { Lang = NCC.NCCL n
  ; size = sizeNCC n
  }

sizeCCC : ∀ {i : Size} {A : 𝔸} → CCC.CCC i A → ℕ
sizeCCC {A = A} (a CCC.CCC.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeCCC cs))
sizeCCC (D CCC.CCC.⟨ cs ⟩) = suc (List.sum (List.map sizeCCC (List⁺.toList cs)))

sizeCCC>0 : ∀ {i : Size} {A : 𝔸} → (ccc : CCC.CCC i A) → sizeCCC ccc > 0
sizeCCC>0 (a CCC.-< cs >-) = s≤s z≤n
sizeCCC>0 (D CCC.⟨ cs ⟩) = s≤s z≤n

SizedCCC : SizedLang
SizedCCC = record
  { Lang = CCC.CCCL
  ; size = sizeCCC
  }

sizeADT : {A : 𝔸} → ADT.ADT A → ℕ
sizeADT (ADT.ADT.leaf v) = suc (sizeRose v)
sizeADT (D ADT.ADT.⟨ l , r ⟩) = suc (sizeADT l + sizeADT r)

SizedADT : SizedLang
SizedADT = record
  { Lang = ADT.ADTL
  ; size = sizeADT
  }

sizeOC : ∀ {i : Size} {A : 𝔸} → OC.OC i A → ℕ
sizeOC {A = A} (a OC.-< cs >-) = suc (atomSize A a + List.sum (List.map sizeOC cs))
sizeOC (D OC.❲ c ❳) = suc (sizeOC c)

sizeWFOC : ∀ {i : Size} {A : 𝔸} → OC.WFOC i A → ℕ
sizeWFOC {A = A} (OC.Root a cs) = suc (atomSize A a + List.sum (List.map sizeOC cs))

SizedWFOC : SizedLang
SizedWFOC = record
  { Lang = OC.WFOCL
  ; size = sizeWFOC
  }

sizeFST : {A : 𝔸} → FST.Impose.SPL A → ℕ
sizeFST (root FST.Impose.◀ features) = 1 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) features)

SizedFST : SizedLang
SizedFST = record
  { Lang = FST.FSTL
  ; size = sizeFST
  }
