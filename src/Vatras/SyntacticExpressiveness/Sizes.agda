open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.SyntacticExpressiveness.Sizes (F : 𝔽) where

open import Data.Nat using (ℕ; suc; zero; _+_)
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
sizeRose (a Rose.-< cs >-) = suc (List.sum (List.map sizeRose cs))

size2CC : ∀ {i : Size} {A : 𝔸} → 2CC.2CC i A → ℕ
size2CC (a 2CC.2CC.-< cs >-) = suc (List.sum (List.map size2CC cs))
size2CC (D 2CC.2CC.⟨ l , r ⟩) = suc (size2CC l + size2CC r)

Sized2CC : SizedLang
Sized2CC = record
  { Lang = 2CC.2CCL
  ; size = size2CC
  }

sizeNCC : ∀ {i : Size} {A : 𝔸} (n : ℕ≥ 2) → NCC.NCC n i A → ℕ
sizeNCC n (a NCC.NCC.-< cs >-) = suc (List.sum (List.map (sizeNCC n) cs))
sizeNCC n (D NCC.NCC.⟨ cs ⟩) = suc (Vec.sum (Vec.map (sizeNCC n) cs))

SizedNCC : ℕ≥ 2 → SizedLang
SizedNCC n = record
  { Lang = NCC.NCCL n
  ; size = sizeNCC n
  }

sizeCCC : ∀ {i : Size} {A : 𝔸} → CCC.CCC i A → ℕ
sizeCCC (a CCC.CCC.-< cs >-) = suc (List.sum (List.map sizeCCC cs))
sizeCCC (D CCC.CCC.⟨ cs ⟩) = suc (List.sum (List.map sizeCCC (List⁺.toList cs)))

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

sizeFST : {A : 𝔸} → FST.Impose.SPL A → ℕ
sizeFST (root FST.Impose.◀ features) = 1 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) features)

SizedFST : SizedLang
SizedFST = record
  { Lang = FST.FSTL
  ; size = sizeFST
  }
