module Example where

open import Data.Nat as ℕ using (ℕ)
open import Data.String as String using (String)
open import Size using (∞)
open import Data.List using ([]; _∷_)

open import Vatras.Framework.Examples using (ℕ-𝔸)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All.FixedAtoms String (Rose ∞) ℕ-𝔸

-- same result
{-
testCCC : 2CC.2CC ∞
testCCC = 0 2CC.-< "Feature" 2CC.⟨ 1 2CC.-< [] >- , 2 2CC.-< [] >- ⟩ ∷ [] >-
-}

open 2CC

testCCC : 2CC ∞
testCCC = 0 -< "Feature" ⟨ 1 -< [] >- , 2 -< [] >- ⟩ ∷ [] >-
