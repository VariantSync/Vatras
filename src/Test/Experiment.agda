{-# OPTIONS --guardedness #-}

module Test.Experiment where

open import Data.List using (List)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; putStrLn; _>>_)
open import Level using (Level; 0ℓ)
open import Function using (_∘_)

open import Test.Example

headline : String → String
headline title = "====[ " ++ title ++ " ]===="

linebreak : ∀ {ℓ : Level} → IO {ℓ} ⊤
linebreak = putStrLn ""

record Experiment (A : Set) : Set₁ where
  field
    name : String
    run : Example A → IO {0ℓ} ⊤
open Experiment public

runAll : {A : Set} → Experiment A → List (Example A) → IO {0ℓ} ⊤
runAll experiment examples = do
  putStrLn (headline ("BEGIN " ++ (name experiment)))
  linebreak
  -- Run and print each example sequentially. Put a linebreak after each example run.
  IO.List.mapM′ ((_>> linebreak) ∘ run experiment) examples
  putStrLn (headline (" END " ++ (name experiment)))
  linebreak

