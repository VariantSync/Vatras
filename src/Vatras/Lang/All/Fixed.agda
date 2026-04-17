open import Vatras.Framework.Definitions using (𝔽; 𝕍)

module Vatras.Lang.All.Fixed (F : 𝔽) (V : 𝕍) where

open import Vatras.Util.Nat.AtLeast using (ℕ≥)

import Vatras.Lang.VariantList
import Vatras.Lang.CCC
import Vatras.Lang.NCC
import Vatras.Lang.2CC
import Vatras.Lang.NADT
import Vatras.Lang.ADT
import Vatras.Lang.ADT.Prop
import Vatras.Lang.OC
import Vatras.Lang.FST
import Vatras.Lang.Gruler
import Vatras.Lang.VT
import Vatras.Lang.PropOC

module VariantList = Vatras.Lang.VariantList V
module CCC = Vatras.Lang.CCC F
module NCC where
  -- Similar as in `Vatras.Lang.All`, we make the arity argument implicit for usablity.
  open Vatras.Lang.NCC F using (NCC; NCCL; Configuration) public
  module _ {n : ℕ≥ 2} where
    open Vatras.Lang.NCC F n hiding (NCC; NCCL; Configuration) public
module 2CC = Vatras.Lang.2CC F
module NADT = Vatras.Lang.NADT F V
module PropADT = Vatras.Lang.ADT.Prop F V
module ADT = Vatras.Lang.ADT F V
module OC = Vatras.Lang.OC F
module FST = Vatras.Lang.FST F
module Gruler = Vatras.Lang.Gruler F
module VT = Vatras.Lang.VT F
module PropOC = Vatras.Lang.PropOC F
