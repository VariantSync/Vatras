open import Data.String as String using (String; _++_)
open import Vatras.Framework.Definitions using (𝔽)
open import Vatras.Util.Nat.AtLeast using (ℕ≥)
module Vatras.Lang.NCC.Show {Dimension : 𝔽} {n : ℕ≥ 2} (show-D : Dimension → String) where

open import Size using (Size)
import Data.Vec as Vec
open import Data.List as List using ([]; _∷_)
open import Data.Product using (_,_)

open import Vatras.Show.Lines
open import Vatras.Lang.NCC Dimension n using (NCC; _⟨_⟩; _-<_>-)

show : ∀ {i} → NCC i (String , String._≟_) → String
show (a -< [] >-) = a
show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (String.intersperse ", " (List.map show es)) ++ ">-"
show (D ⟨ cs ⟩) = show-D D ++ "⟨" ++ (String.intersperse ", " (List.map show (Vec.toList cs))) ++ "⟩"


pretty : ∀ {i : Size} → NCC i (String , String._≟_) → Lines
pretty (a -< [] >-) = > a
pretty (a -< es@(_ ∷ _) >-) = do
  > a ++ "-<"
  indent 2 do
    intersperseCommas (List.map pretty es)
  > ">-"
pretty (D ⟨ cs ⟩) = do
  > show-D D ++ "⟨"
  indent 2 do
    intersperseCommas (List.map pretty (Vec.toList cs))
  > "⟩"
