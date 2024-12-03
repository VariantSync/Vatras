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
import Vatras.Lang.FST
import Vatras.Lang.Gruler

open import Data.Empty.Polymorphic using (⊥)
open import Vatras.Util.Nat.AtLeast using (ℕ≥)
open import Size using (∞)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)
open import Vatras.Framework.Variants using (Rose)

module VariantList where
  open Vatras.Lang.VariantList hiding (Configuration) public
  module _ where
    open Vatras.Lang.VariantList (λ _ → ⊥) using (Configuration) public

module CCC where
  open Vatras.Lang.CCC using (CCC; CCCL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.CCC F hiding (CCC; CCCL; Configuration) public

module NCC where
  open Vatras.Lang.NCC using (NCC; NCCL; Configuration) public
  module _ {F : 𝔽} {n : ℕ≥ 2} where
    open Vatras.Lang.NCC F n hiding (NCC; NCCL; Configuration) public

module 2CC where
  open Vatras.Lang.2CC using (2CC; 2CCL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.2CC F hiding (2CC; 2CCL; Configuration) public

module NADT where
  open Vatras.Lang.NADT using (NADT; NADTL) public
  module _ (F : 𝔽) where
    open Vatras.Lang.NADT F (λ _ → ⊥) using (Configuration) public
  module _ {F : 𝔽} {V : 𝕍} where
    open Vatras.Lang.NADT F V hiding (NADT; NADTL; Configuration) public

module ADT where
  open Vatras.Lang.ADT using (ADT; ADTL) public
  module _ (F : 𝔽) where
    open Vatras.Lang.ADT F (λ _ → ⊥) using (Configuration) public
  module _ {F : 𝔽} {V : 𝕍} where
    open Vatras.Lang.ADT F V hiding (ADT; ADTL; Configuration) public

module OC where
  open Vatras.Lang.OC using (OC; OCL; WFOC; WFOCL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.OC F hiding (OC; OCL; WFOC; WFOCL; Configuration) public

module Gruler where
  open Vatras.Lang.Gruler using (Gruler; GrulerL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.Gruler F hiding (Gruler; GrulerL; Configuration) public

-- TODO deal with the anoying Impose module
module FST where
  open Vatras.Lang.FST using (FST; FSTL; Configuration) public
  module _ where
    open Vatras.Lang.FST ⊥ using (_．_; branches) public
  module _ {F : 𝔽} where
    open Vatras.Lang.FST F hiding (FST; FSTL; Configuration; _．_; branches) public
