module Lang.All where

import Lang.VariantList
module VariantList = Lang.VariantList

import Lang.CCC
module CCC = Lang.CCC

import Lang.NCC
module NCC = Lang.NCC

import Lang.2CC
module 2CC = Lang.2CC

import Lang.NADT
module NADT = Lang.NADT

import Lang.ADT
module ADT = Lang.ADT

module OC where
  open import Lang.OC public
  open Lang.OC.Sem public

module FST where
  open import Lang.FST renaming (FSTL-Sem to ⟦_⟧) public
