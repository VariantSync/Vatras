module Lang.All where

open import Size using (∞)
open import Framework.Definitions using (𝔽; 𝔸)
open import Framework.Variants using (Rose)

import Lang.VariantList
import Lang.CCC
import Lang.NCC
import Lang.2CC
import Lang.NADT
import Lang.ADT
import Lang.OC

module VariantList = Lang.VariantList
module CCC = Lang.CCC
module NCC = Lang.NCC
module 2CC = Lang.2CC
module NADT = Lang.NADT
module ADT = Lang.ADT
module OC = Lang.OC

module FST where
  open import Lang.FST hiding (FST; FSTL-Sem; Conf) public

  Configuration = Lang.FST.Conf

  ⟦_⟧ : ∀ {F : 𝔽} {A : 𝔸} → Impose.SPL F A → Configuration F → Rose ∞ A
  ⟦_⟧ {F} = Lang.FST.FSTL-Sem F
