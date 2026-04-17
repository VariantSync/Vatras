open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.FST.Util (F : 𝔽) (A : 𝔸) where

open import Data.Bool using (true; false)
open import Data.List as List using ([]; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_; refl)

import Vatras.Lang.FST
open Vatras.Lang.FST F using (Configuration)
open Vatras.Lang.FST.Impose F A using (select; impl; name; _::_)

select≗filter
  : (config : Configuration)
  → select config ≗ List.map impl ∘ List.filterᵇ (config ∘ name)
select≗filter config [] = refl
select≗filter config ((name :: impl) ∷ fs) with config name
select≗filter config ((name :: impl) ∷ fs) | true = Eq.cong (impl ∷_) (select≗filter config fs)
select≗filter config ((name :: impl) ∷ fs) | false = select≗filter config fs
