open import Framework.Definitions using (𝕍)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module defines a compiler from NCC to NCC where the input and output expression
can have any arities, in particular different ones.
This compiler is a simple composition of the ShrinkTo2 and Grow compiler.
This means, given an n-ary expression,
it is first reduced to a 2-ary expression
and then pumped to an m-ary expression.
-}
module Translation.Lang.NCC.NCC-to-NCC (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ∞)
import Util.AuxProofs as ℕ
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Util.Vec as Vec

open import Lang.All.Generic Variant Artifact∈ₛVariant
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

open import Translation.Lang.NCC.ShrinkTo2 Variant Artifact∈ₛVariant using (shrinkTo2Compiler)
open import Translation.Lang.NCC.Grow Variant Artifact∈ₛVariant using (growFrom2Compiler)

NCC→NCC : ∀ {i : Size} {D : 𝔽} → (n m : ℕ≥ 2) → LanguageCompiler (NCCL {i} n D) (NCCL m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
NCC→NCC n m = shrinkTo2Compiler n ⊕ growFrom2Compiler m

NCC≽NCC : ∀ {i : Size} {D : 𝔽} → (n m : ℕ≥ 2) → NCCL m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) ≽ NCCL {i} n D
NCC≽NCC n m = expressiveness-from-compiler (NCC→NCC n m)
