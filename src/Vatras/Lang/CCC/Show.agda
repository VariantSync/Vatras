open import Vatras.Framework.Definitions using (𝔽; STRING)
module Vatras.Lang.CCC.Show {Dimension : 𝔽} where

open import Size using (Size)
open import Data.List as List using ([]; _∷_)
import Data.List.NonEmpty as List⁺
open import Data.Product using (_,_)
open import Data.String as String using (String; _++_)

open import Vatras.Show.Lines hiding (map)
open import Vatras.Lang.CCC Dimension using (CCC; _-<_>-; _⟨_⟩)

show : ∀ {i} → (Dimension → String) → CCC i STRING → String
show _ (a -< [] >-) = a
show show-D (a -< es@(_ ∷ _) >- ) = a ++ "-<" ++ (List.foldl _++_ "" (List.map (show show-D) es)) ++ ">-"
show show-D (D ⟨ es ⟩) = show-D D ++ "⟨" ++ (String.intersperse ", " (List⁺.toList (List⁺.map (show show-D) es))) ++ "⟩"

pretty : ∀ {i : Size} → (Dimension → String) → CCC i STRING → Lines
pretty show-D (a -< [] >-) = > a
pretty show-D (a -< es@(_ ∷ _) >-) = do
  > a ++ "-<"
  indent 2 do
    intersperseCommas (List.map (pretty show-D) es)
  > ">-"
pretty show-D (D ⟨ cs ⟩) = do
  > show-D D ++ "⟨"
  indent 2 do
    intersperseCommas (List.map (pretty show-D) (List⁺.toList cs))
  > "⟩"
