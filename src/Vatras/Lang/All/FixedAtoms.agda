open import Vatras.Framework.Definitions using (𝔽; 𝕍; 𝔸)

module Vatras.Lang.All.FixedAtoms (F : 𝔽) (V : 𝕍) (A : 𝔸) where

open import Size using (Size)

open import Vatras.Util.Nat.AtLeast using (ℕ≥)
import Vatras.Lang.All.Fixed F V as Lang

module VariantList where
  VariantList = Lang.VariantList.VariantList A
  Clone-and-Own = Lang.VariantList.Clone-and-Own A
  open Lang.VariantList hiding (VariantList; Clone-and-Own) public

module CCC where
  CCC : Size → Set₁
  CCC i = Lang.CCC.CCC i A
  open Lang.CCC hiding (CCC) public

module NCC where
  NCC : ℕ≥ 2 → Size → Set₁
  NCC n i = Lang.NCC.NCC n i A
  open Lang.NCC hiding (NCC) public

module 2CC where
  2CC : Size → Set₁
  2CC i = Lang.2CC.2CC i A
  open Lang.2CC hiding (2CC) public

module NADT where
  NADT : Size → Set₁
  NADT i = Lang.NADT.NADT i A
  open Lang.NADT hiding (NADT) public

module ADT where
  ADT = Lang.ADT.ADT A
  open Lang.ADT hiding (ADT) public

module OC where
  OC : Size → Set₁
  OC i = Lang.OC.OC i A
  open Lang.OC hiding (OC) public

module FST where
  FST : Size → Set₁
  FST i = Lang.FST.FST i A
  open Lang.FST hiding (FST) public

module Gruler where
  Gruler : Size → Set₁
  Gruler i = Lang.Gruler.Gruler i A
  open Lang.Gruler hiding (Gruler) public
