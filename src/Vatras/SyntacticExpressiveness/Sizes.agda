open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.SyntacticExpressiveness.Sizes (F : 𝔽) (A : 𝔸) where

open import Data.Nat using (ℕ; suc; zero; _+_)
import Data.List as List
open import Size using (∞)

open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.SyntacticExpressiveness A using (SizedLang)

size2CC : ∀ {i} → 2CC.2CC i A → ℕ
size2CC (a 2CC.2CC.-< cs >-) = suc (List.sum (List.map size2CC cs))
size2CC (D 2CC.2CC.⟨ l , r ⟩) = suc (size2CC l + size2CC r)

Sized2CC : SizedLang
Sized2CC = record
  { Lang = 2CC.2CCL
  ; size = size2CC
  }

sizeADT : ADT.ADT A → ℕ
sizeADT (ADT.ADT.leaf v) = suc zero -- TODO also count the variant
sizeADT (D ADT.ADT.⟨ l , r ⟩) = suc (sizeADT l + sizeADT r)

SizedADT : SizedLang
SizedADT = record
  { Lang = ADT.ADTL
  ; size = sizeADT
  }
