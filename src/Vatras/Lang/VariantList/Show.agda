open import Vatras.Framework.Definitions using (𝕍; 𝔸)
module Vatras.Lang.VariantList.Show {V : 𝕍} where

import Data.List as List
open import Data.List.NonEmpty using (_∷_)
open import Data.Product using (_,_)
open import Data.String as String using (String; _++_; intersperse)

open import Vatras.Show.Lines
open import Vatras.Lang.VariantList V using (VariantList)

pretty : {A : 𝔸} → (V A → String) → VariantList A → Lines
pretty {A} pretty-variant (v ∷ vs) = do
  > "[ " ++ pretty-variant v
  lines (List.map (λ v → > ", " ++ pretty-variant v) vs)
  > "]"
