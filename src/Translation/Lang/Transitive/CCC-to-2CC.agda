module Translation.Lang.Transitive.CCC-to-2CC where

open import Size using (Size; ∞)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_)
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔽)
open import Framework.Variants using (Rose)
open import Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Util.Nat.AtLeast using (sucs)

open import Lang.All
open CCC using (CCCL)
open 2CC using (2CCL)

open import Translation.Lang.CCC-to-NCC using (CCC→NCC)
import Translation.Lang.NCC-to-2CC
open Translation.Lang.NCC-to-2CC.2Ary using (NCC→2CC)


CCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (CCCL {i} D) (2CCL (D × ℕ))
CCC→2CC = CCC→NCC (sucs zero) ⊕ NCC→2CC

2CC≽CCC : ∀ {D : 𝔽} → 2CCL (D × ℕ) ≽ CCCL D
2CC≽CCC = expressiveness-from-compiler CCC→2CC
