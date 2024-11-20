open import Vatras.Framework.Definitions using (𝔽)
open import Data.String as String using (String; _++_)
module Vatras.Lang.OC.Show {Option : 𝔽} (print-opt : Option → String) where

open import Size using (Size)
open import Function using (_∘_)
open import Data.Product using (_,_)
open import Data.List as List using ([]; _∷_)

open import Vatras.Show.Lines hiding (map)
open import Vatras.Lang.OC Option using (OC; _❲_❳; _-<_>-; WFOC; forgetWF)

show-oc : ∀ {i : Size} → OC i (String , String._≟_) → String
show-oc (s -< [] >-) = s
show-oc (s -< es@(_ ∷ _) >-) = s ++ "-<" ++ (String.intersperse ", " (List.map show-oc es)) ++ ">-"
show-oc (O ❲ e ❳) = print-opt O ++ "❲" ++ show-oc e ++ "❳"

show-wfoc : ∀ {i : Size} → WFOC i (String , String._≟_) → String
show-wfoc = show-oc ∘ forgetWF

pretty-oc : ∀ {i : Size} → OC i (String , String._≟_) → Lines
pretty-oc (s -< [] >-) = > s
pretty-oc (s -< es@(_ ∷ _) >-) = do
  > s ++ "-<"
  indent 2 do
    intersperseCommas (List.map pretty-oc es)
  > ">-"
pretty-oc (O ❲ e ❳) = do
  > print-opt O ++ "❲"
  indent 2 (pretty-oc e)
  > "❳"

pretty-wfoc : ∀ {i : Size} → WFOC i (String , String._≟_) → Lines
pretty-wfoc = pretty-oc ∘ forgetWF
