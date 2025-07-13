open import Vatras.Framework.Definitions
open import Data.String as String using (String; _++_)
module Vatras.Lang.2CC.Show {Dimension : 𝔽} (show-D : Dimension → String) where

open import Size using (Size)
open import Data.Product using (_,_)
open import Data.List as List using ([]; _∷_)

open import Vatras.Show.Lines
open import Vatras.Lang.2CC Dimension using (2CC; _⟨_,_⟩; _-<_>-)

show : ∀ {i} → 2CC i STRING → String
show (a -< [] >-) = a
show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (String.intersperse ", " (List.map show es)) ++ ">-"
show (D ⟨ l , r ⟩) = show-D D ++ "⟨" ++ (show l) ++ ", " ++ (show r) ++ "⟩"

pretty : ∀ {i : Size} → 2CC i STRING → Lines
pretty (a -< [] >-) = > a
pretty (a -< es@(_ ∷ _) >-) = do
  > a ++ "-<"
  indent 2 do
    intersperseCommas (List.map pretty es)
  > ">-"
pretty (D ⟨ l , r ⟩) = do
  > show-D D ++ "⟨"
  indent 2 do
    appendToLastLine "," (pretty l)
    pretty r
  > "⟩"
