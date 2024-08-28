module Vatras.Translation.Lang.Transitive.CCC-to-2CC where

open import Size using (Size; ∞)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_)
open import Vatras.Framework.Compiler using (LanguageCompiler; _⊕_)
open import Vatras.Framework.Definitions using (𝔽)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Util.Nat.AtLeast using (sucs)

open import Vatras.Lang.All
open CCC using (CCCL)
open 2CC using (2CCL)

open import Vatras.Translation.Lang.CCC-to-NCC using (CCC→NCC)
import Vatras.Translation.Lang.NCC-to-2CC
open Vatras.Translation.Lang.NCC-to-2CC.2Ary using (NCC→2CC)


CCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (CCCL {i} D) (2CCL (D × ℕ))
CCC→2CC = CCC→NCC (sucs zero) ⊕ NCC→2CC

2CC≽CCC : ∀ {D : 𝔽} → 2CCL (D × ℕ) ≽ CCCL D
2CC≽CCC = expressiveness-from-compiler CCC→2CC
