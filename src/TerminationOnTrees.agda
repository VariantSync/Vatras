module TerminationOnTrees where

open import Data.List
open import Data.Nat

data Tree (A : Set) : Set where
  node : A → List (Tree A) → Tree A

-- Termination checking fails for all of these
-- Is it because lists can be infinite
size-fold : {A : Set} → ℕ → Tree A → ℕ

size : {A : Set} → Tree A → ℕ
size {A} (node _ cs) = suc (foldl size-fold zero cs)

size-fold s n = s + size n

map-tree : {A B : Set} → (f : A → B) → Tree A → Tree B
map-tree f (node v cs) = node (f v) (map (map-tree f) cs)

-- does not work
--map-tree-terminating : {A B : Set} → (f : A → B) → Tree A → Tree B
--map-tree-terminating f (node v []) = node (f v) []
--map-tree-terminating f (node v (x ∷ xs)) = node (f v) (map-tree-terminating f x ∷ []) -- (map (map-tree-terminating f) xs))

-- Binary tree
data BinTree (A : Set) : Set where
  leaf : A → BinTree A
  node : A → BinTree A → BinTree A → BinTree A

-- This terminates!!
map-tree-bin : {A B : Set} → (f : A → B) → BinTree A → BinTree B
map-tree-bin f (leaf a) = leaf (f a)
map-tree-bin f (node a l r) = node (f a) (map-tree-bin f l) (map-tree-bin f r)

-- Does it work with standard-library rose trees?

