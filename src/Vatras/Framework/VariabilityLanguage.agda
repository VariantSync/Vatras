{-|
This module formalizes languages for static variability.
-}
module Vatras.Framework.VariabilityLanguage where

open import Vatras.Framework.Definitions

{-|
A common semantics for variability languages is
a function that configures expressions "E A" to
variants "V A" via configurations "C", where "A"
is a fixed set of atoms.
Please have a look at our paper for an in-depth
discussion of this definition.
-}
𝔼-Semantics : 𝕍 → ℂ → 𝔼 → Set₁
𝔼-Semantics V C E = ∀ {A : 𝔸} → E A → C → V A

{-|
A variability language is a 3-tuple consisting of
a syntax, a configuration language, and semantics.
-}
record VariabilityLanguage (V : 𝕍) : Set₂ where
  constructor ⟪_,_,_⟫
  field
    Expression : 𝔼
    Config     : ℂ
    Semantics  : 𝔼-Semantics V Config Expression
open VariabilityLanguage public
