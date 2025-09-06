{-# OPTIONS --allow-unsolved-metas #-}
module Vatras.Util.Nat.Diagonalization where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≗_)

diagonalization : ℕ × ℕ → ℕ
diagonalization = {!!}

diagonalization⁻¹ : ℕ → ℕ × ℕ
diagonalization⁻¹ = {!!}

diagonalization-injective : diagonalization⁻¹ ∘ diagonalization ≗ id
diagonalization-injective = {!!}
