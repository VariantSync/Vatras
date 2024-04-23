module Test.Examples.Variants where

open import Data.Fin using (zero; suc)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.List using (List; []; _∷_)
open import Data.String as String using (String)
open import Size using (∞)
open import Framework.VariabilityLanguage using (artifact)
open import Framework.VariantMap using (VMap)

open import Test.Example

𝕍-123 : Example (VMap (ℕ , ℕ._≟_) 2)
𝕍-123 = "123" ≔ set
  where set : VMap (ℕ , ℕ._≟_) 2
        set zero = artifact 1 []
        set (suc zero) = artifact 2 []
        set (suc (suc zero)) = artifact 3 []

𝕍-lr : Example (VMap (String , String._≟_) 1)
getName 𝕍-lr = "lr"
get 𝕍-lr zero = artifact "left" []
get 𝕍-lr (suc zero) = artifact "right" []
