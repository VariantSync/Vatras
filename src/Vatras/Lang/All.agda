{-|
This module reexports all our language definitions as new modules.
Instead of directly importing the language modules,
we recommend importing this module if you do not want to apply the module parameters.

For convenience, we change explicit module parameters to implicit ones where useful.
The rule of thumb is:
  Types use explicit arguments whereas functions use implicit arguments.
In case you want to instantiate these module parameters with a fixed value,
you can use `Vatras.Lang.All.Fixed` instead of this module.
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
import Vatras.Lang.VT
import Vatras.Lang.PropOC

open import Data.Empty.Polymorphic using (⊥)
open import Vatras.Util.Nat.AtLeast using (ℕ≥)
open import Size using (∞)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)
open import Vatras.Framework.Variants using (Rose)

{-
Some definitions do not make use of the module parameter.
In such cases explicit arguments would be confusing and implicit paramters would lead to unsolved metas.
Hence, we assert that these parameters are unused by passing `⊥` for `𝔽` or `λ _ → ⊥` for `𝔸`.
-}

module VariantList where
  open Vatras.Lang.VariantList using (VariantList; VariantListL; Clone-and-Own) public
  open Vatras.Lang.VariantList (λ _ → ⊥) using (Configuration) public
  module _ {V : 𝕍} where
    open Vatras.Lang.VariantList V hiding (VariantList; VariantListL; Clone-and-Own; Configuration) public

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

module FST where
  open Vatras.Lang.FST using (FSTL; FST; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.FST F using (⟦_⟧) public
    module Impose = Vatras.Lang.FST.Impose F

module Gruler where
  open Vatras.Lang.Gruler using (Gruler; GrulerL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.Gruler F hiding (Gruler; GrulerL; Configuration) public

module VT where
  open Vatras.Lang.VT using (VT; UnrootedVT; VTL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.VT F hiding (VT; UnrootedVT; VTL; Configuration) public

module PropOC where
  open Vatras.Lang.PropOC using (PropOC; PropOCL; WFPropOC; WFPropOCL; Configuration) public
  module _ {F : 𝔽} where
    open Vatras.Lang.PropOC F hiding (PropOC; PropOCL; WFPropOC; WFPropOCL; Configuration) public
