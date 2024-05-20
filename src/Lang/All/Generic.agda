open import Framework.Definitions using (𝕍; 𝔽; 𝔸)
open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Lang.All.Generic (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Size using (∞)

open import Framework.Variants using (Rose)

module VariantList where
  open import Lang.VariantList Variant public

module CCC where
  open import Lang.CCC public
  open Lang.CCC.Sem Variant Artifact∈ₛVariant public

module NCC where
  open import Lang.NCC public
  open Lang.NCC.Sem Variant Artifact∈ₛVariant public

module 2CC where
  open import Lang.2CC public
  open Lang.2CC.Sem Variant Artifact∈ₛVariant public

module NADT where
  open import Lang.NADT public

module ADT where
  open import Lang.ADT public

module OC where
  open import Lang.OC public
  open Lang.OC.Sem Variant Artifact∈ₛVariant public

module FST where
  open import Lang.FST hiding (FST; FSTL-Sem; Conf) public

  Configuration = Lang.FST.Conf

  ⟦_⟧ : ∀ {F : 𝔽} {A : 𝔸} → Impose.SPL F A → Configuration F → Rose ∞ A
  ⟦_⟧ {F} = Lang.FST.FSTL-Sem F
