{-# OPTIONS --guardedness #-}

module Show.Print where

open import Data.Nat using (ℕ)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; putStrLn)
open IO.List using (mapM′)
open import Level using (0ℓ)

open import Show.Lines using (Lines; align; content; raw-lines)

open import Data.Nat.Show using (show)
open import Data.List using (length)

open import Function using (_∘_)

print : ℕ → Lines → IO {0ℓ} ⊤
print width = mapM′ (putStrLn ∘ content ∘ align width) ∘ raw-lines
