module Data.ReversedList where

open import Data.List using (List; []; [_]; _++_)

data ReversedList (A : Set) : Set where
  []  :                      ReversedList A
  _∷_ : ReversedList A → A → ReversedList A

maprl : ∀ {A B : Set} → (f : A → B) → ReversedList A → ReversedList B
maprl f []       = []
maprl f (xs ∷ x) = maprl f xs ∷ f x

toList : ∀ {A : Set} → ReversedList A → List A
toList []       = []
toList (xs ∷ x) = toList xs ++ [ x ]
