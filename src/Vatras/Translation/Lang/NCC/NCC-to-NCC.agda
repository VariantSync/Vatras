{-
This module defines a compiler from NCC to NCC where the input and output expression
can have any arities, in particular different ones.
This compiler is a simple composition of the ShrinkTo2 and Grow compiler.
This means, given an n-ary expression,
it is first reduced to a 2-ary expression
and then pumped to an m-ary expression.
-}
module Vatras.Translation.Lang.NCC.NCC-to-NCC where

open import Size using (Size; ∞)
open import Data.Empty using (⊥-elim)
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Vatras.Framework.Compiler using (LanguageCompiler; _⊕_)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
import Vatras.Util.AuxProofs as ℕ
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Vatras.Util.Vec as Vec

open import Vatras.Lang.All
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

open import Vatras.Translation.Lang.NCC.ShrinkTo2 using (shrinkTo2Compiler)
open import Vatras.Translation.Lang.NCC.Grow using (growFrom2Compiler)

NCC→NCC : ∀ {i : Size} {D : 𝔽} → (n m : ℕ≥ 2) → LanguageCompiler (NCCL n D {i}) (NCCL m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
NCC→NCC n m = shrinkTo2Compiler n ⊕ growFrom2Compiler m

NCC≽NCC : ∀ {i : Size} {D : 𝔽} → (n m : ℕ≥ 2) → NCCL m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) ≽ NCCL n D {i}
NCC≽NCC n m = expressiveness-from-compiler (NCC→NCC n m)
