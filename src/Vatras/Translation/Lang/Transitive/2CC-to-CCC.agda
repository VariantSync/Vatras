module Vatras.Translation.Lang.Transitive.2CC-to-CCC where

open import Size using (Size; ∞)
open import Data.Nat using (zero)
open import Vatras.Framework.Compiler using (LanguageCompiler; _⊕_)
open import Vatras.Framework.Definitions using (𝔽)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Util.Nat.AtLeast using (sucs)

open import Vatras.Lang.All
open CCC using (CCCL)
open 2CC using (2CCL)

import Vatras.Translation.Lang.2CC-to-NCC
open Vatras.Translation.Lang.2CC-to-NCC.2Ary using (2CC→NCC)
open import Vatras.Translation.Lang.NCC-to-CCC using (NCC→CCC)


2CC→CCC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (2CCL {i} D) (CCCL D)
2CC→CCC = 2CC→NCC ⊕ NCC→CCC (sucs zero)

CCC≽2CC : ∀ {D : 𝔽} → CCCL D ≽ 2CCL D
CCC≽2CC = expressiveness-from-compiler 2CC→CCC
