module Data.ReversedList where

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (inspect)

data ReversedList (A : Set) : Set where
  []  :                      ReversedList A
  _∷_ : ReversedList A → A → ReversedList A

data ReversedList⁺ (A : Set) : Set where
  _∷_ : ReversedList A → A → ReversedList⁺ A

maprl : ∀ {A B : Set} → (f : A → B) → ReversedList A → ReversedList B
maprl f []       = []
maprl f (xs ∷ x) = maprl f xs ∷ f x

toReversedList : ∀ {A : Set} → ReversedList A → List A
toReversedList [] = []
toReversedList (xs ∷ x) = x ∷ toReversedList xs

toList : ∀ {A : Set} → ReversedList A → List A
toList = Data.List.reverse ∘ toReversedList

toReversedList⁺ : ∀ {A : Set} → ReversedList⁺ A → List⁺ A
toReversedList⁺ ([] ∷ t) = t ∷ []
toReversedList⁺ ((xs ∷ x) ∷ t) = t ∷ toReversedList (xs ∷ x)

toList⁺ : ∀ {A : Set} → ReversedList⁺ A → List⁺ A
toList⁺ = Data.List.NonEmpty.reverse ∘ toReversedList⁺
