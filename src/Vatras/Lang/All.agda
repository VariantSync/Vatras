{-|
This module reexports all our language definitions as new modules.
If you intend to work with more than one language in a file
we recommend using this module to easily import the languages you need.
-}
module Vatras.Lang.All where

import Vatras.Lang.VariantList
import Vatras.Lang.CCC
import Vatras.Lang.NCC
import Vatras.Lang.2CC
import Vatras.Lang.NADT
import Vatras.Lang.ADT
import Vatras.Lang.OC
import Vatras.Lang.Gruler

module VariantList = Vatras.Lang.VariantList
module CCC         = Vatras.Lang.CCC
module NCC         = Vatras.Lang.NCC
module 2CC         = Vatras.Lang.2CC
module NADT        = Vatras.Lang.NADT
module ADT         = Vatras.Lang.ADT
module OC          = Vatras.Lang.OC
module Gruler      = Vatras.Lang.Gruler

module FST where
  open import Size using (∞)
  open import Vatras.Framework.Definitions using (𝔽; 𝔸)
  open import Vatras.Framework.Variants using (Rose)
  open import Vatras.Lang.FST hiding (⟦_⟧) public

  ⟦_⟧ : ∀ {F : 𝔽} {A : 𝔸} → Impose.SPL F A → Configuration F → Rose ∞ A
  ⟦_⟧ {F} = Vatras.Lang.FST.⟦_⟧ F
