open import Vatras.Framework.Definitions using (𝔽; 𝕍)

module Vatras.Lang.All.Fixed (F : 𝔽) (V : 𝕍) where

import Vatras.Lang.VariantList
import Vatras.Lang.CCC
import Vatras.Lang.NCC
import Vatras.Lang.2CC
import Vatras.Lang.NADT
import Vatras.Lang.ADT
import Vatras.Lang.OC
import Vatras.Lang.FST
import Vatras.Lang.Gruler

module VariantList = Vatras.Lang.VariantList V
module CCC = Vatras.Lang.CCC F
module NCC = Vatras.Lang.NCC F
module 2CC = Vatras.Lang.2CC F
module NADT = Vatras.Lang.NADT F V
module ADT = Vatras.Lang.ADT F V
module OC = Vatras.Lang.OC F
module FST = Vatras.Lang.FST F
module Gruler = Vatras.Lang.Gruler F
