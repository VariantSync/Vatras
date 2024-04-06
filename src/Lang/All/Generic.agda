{-# OPTIONS --sized-types #-}

open import Framework.Definitions using (𝕍)
open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Lang.All.Generic (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

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
  open import Lang.NADT renaming (NADTVL to NADTL) public

module ADT where
  open import Lang.ADT public

module OC where
  open import Lang.OC public
  open Lang.OC.Sem Variant Artifact∈ₛVariant public
