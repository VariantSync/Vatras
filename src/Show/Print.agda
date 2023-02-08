{-# OPTIONS --guardedness #-}

module Show.Print where

open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; putStrLn)
open IO.List using (mapM′)
open import Level using (0ℓ)

open import Show.Lines using (Lines)

open import Data.Nat.Show using (show)
open import Data.List using (length)

print : Lines → IO {0ℓ} ⊤
print = mapM′ putStrLn
