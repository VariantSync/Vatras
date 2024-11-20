open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Lang.2CC.Util {Dimension : 𝔽} where

open import Size using (Size)
open import Data.List using (List; _∷_; concatMap; _++_)

open import Vatras.Lang.2CC Dimension using (2CC; _⟨_,_⟩; _-<_>-)

{-|
Recursively, collect all dimensions used in a binary CC expression
-}
dims : ∀ {i : Size} {A : 𝔸} → 2CC i A → List Dimension
dims (_ -< es >-)  = concatMap dims es
dims (D ⟨ l , r ⟩) = D ∷ (dims l ++ dims r)
