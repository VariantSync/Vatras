open import Vatras.Framework.Definitions using (𝔽; 𝕍; 𝔸)
module Vatras.Lang.ADT.Show {F : 𝔽} {V : 𝕍} where

open import Data.String as String using (String; _++_)

open import Vatras.Show.Lines
open import Vatras.Lang.ADT F V using (ADT; leaf; _⟨_,_⟩)

{-|
Pretty printer for ADTs.
-}
pretty : {A : 𝔸} → (V A → String) → (F → String) → ADT A → Lines
pretty pretty-variant show-F (leaf v) = > pretty-variant v
pretty pretty-variant show-F (D ⟨ l , r ⟩) = do
  > show-F D ++ "⟨"
  indent 2 do
    appendToLastLine "," (pretty pretty-variant show-F l)
    pretty pretty-variant show-F r
  > "⟩"
