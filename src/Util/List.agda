module Util.List where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; NonZero)
open import Data.List using (List; lookup; length)
open import Data.List.NonEmpty using (List⁺; toList)
open import Util.AuxProofs using (minFinFromLimit; clamp)

-- Selects the alternative at the given tag.
lookup-clamped : {A : Set} → ℕ → List⁺ A → A
lookup-clamped n list⁺ =
  let list = toList list⁺
   in lookup list (clamp (length list) n)
