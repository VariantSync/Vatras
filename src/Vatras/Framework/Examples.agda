module Vatras.Framework.Examples where

open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_)

open import Vatras.Framework.Definitions using (𝔸)

ℕ-𝔸 : 𝔸
ℕ-𝔸 = ℕ , ℕ._≟_
