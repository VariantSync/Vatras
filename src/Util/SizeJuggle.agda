{-
Module with functions for assisting Agda's type checker
when it comes to checking sized types.
Sometimes we need to help a little with explicit type annotations
and safe casts.

This module is called juggling because sometimes Agda can magically convert between the two independent types Size and Size< which we can never do manually.
But sometimes Agda fails.
We can help it with some id functions that have the right type signature though.
-}
module Util.SizeJuggle where

-- to get ⊔ˢ type \lub\^s
-- remember to press ^ button twice!
open import Size using (Size; SizeUniv; Size<_; ↑_; _⊔ˢ_)
open import Util.Existence using (∃-Size; _,_)
open import Data.List
  using (List; []; _∷_)
  renaming (map to mapl)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)

-- We consider a type as bounded if it is parameterized in a size.
Bounded : Set₁
Bounded = Size → Set

record Weaken (B : Bounded) : Set where
  field
    to-larger : ∀ (weaker-bound  : Size)
                  (current-bound : Size< weaker-bound)
                  (e : B current-bound)
                  ------------------------------------
                → B weaker-bound

    -- we cannot build to-max from to-larger because the maximum is not strictly larger than either i or j. It is equal to one of them.
    -- This is a result of not being able to prove i≤i⊔j (see above).
    to-max :    ∀ (i j : Size)
                  (e : B i)
                  ------------
                → B (i ⊔ˢ j)
open Weaken public

-- A size is smaller than itself + 1.
i<↑i : (i : Size) → Size< (↑ i)
i<↑i i = i

i<↑max : ∀ (i j : Size) → Size< (↑ (i ⊔ˢ j))
i<↑max i _ = i

i<↑i-list :
    (B : Bounded)
  → (i : Size)
  → List (B i)
  → List (B (i<↑i i))
i<↑i-list _ _ l = l

data _≡ˢ_ (i : Size) : Size → Set where
  instance reflˢ : i ≡ˢ i

data _≤ˢ_ : Size → Size → Set where
  equal : ∀ {i : Size}
      ------
    → i ≤ˢ i

  smaller : ∀ {i : Size}
    → {j : Size< i}
      -------------
    → j ≤ˢ i

-- Equivalence is not decidable because we have no way to inspect a size.
-- It is just an opaque name to us.
-- _≟_ : ∀ (i j : Size) → Dec (i ≡ˢ j)

-- There is also no way to prove that sizes must be equal or one must be larger than the other one.
-- i≤i⊔j :
--     ∀ (i j : Size)
--     --------------
--   → i ≤ˢ (i ⊔ˢ j)

trans : (i : Size) (j : Size< i) (k : Size< j) → {- k is -} Size< i
trans i j k = k


weaken-by-1 : ∀ {B : Bounded} {i : Size}
  → (Weaken B)
  → (e : B i)
    ---------
  → B (↑ i)
weaken-by-1 {i = i} weaken e = to-larger weaken (↑ i) (i<↑i i) e

weaken-to-↑max : ∀ {B : Bounded}
  → (Weaken B)
  → (i j : Size)
  → B i
    --------------
  → B (↑ (i ⊔ˢ j))
weaken-to-↑max weaken i j e =
   -- Version using to-larger instead of to-max
   --to-larger weaken (↑ (i ⊔ˢ j)) (i<↑max i j) e
   weaken-by-1 weaken (to-max weaken i j e)

weaken-to-smaller-↑max : ∀ {B : Bounded}
  → (Weaken B)
  → (i j : Size)
  → B i
  → B (i<↑i (i ⊔ˢ j))
weaken-to-smaller-↑max weaken = to-max weaken

sym-max : ∀ {B : Bounded} {i j : Size}
  → B (i ⊔ˢ j)
    ----------
  → B (j ⊔ˢ i)
sym-max max = max

sym-↑max : ∀ {B : Bounded}
  → (i j : Size)
  → B (↑ (i ⊔ˢ j))
    --------------
  → B (↑ (j ⊔ˢ i))
sym-↑max _ _ max = max

sym-smaller-↑max :
  ∀ (B : Bounded)
  → (i j : Size)
  → B (i<↑i (i ⊔ˢ j))
    --------------
  → B (i<↑i (j ⊔ˢ i))
sym-smaller-↑max _ _ _ max = max

-- Functions for Lists

weaken-list : ∀ {B : Bounded}
  → Weaken B
  → (i : Size)
  → (j : Size< i)
  → List (B j)
    -------------
  → List (B i)
weaken-list w i j l = mapl (to-larger w i j) l

weaken-list-max : ∀ {B : Bounded}
  → Weaken B
  → (i j : Size)
  → List (B i)
    -----------------
  → List (B (i ⊔ˢ j))
weaken-list-max w i j l = mapl (to-max w i j) l

prepend-sized : ∀ {B : Bounded}
  → Weaken B
  → (i j : Size)
  → B i
  → List (B j)
    -----------------
  → List (B (i ⊔ˢ j))
prepend-sized {B} w i j h t =
  let sized-head : B (i ⊔ˢ j)
      sized-head = to-max w i j h

      sized-tail : List (B (i ⊔ˢ j))
      sized-tail = weaken-list-max w j i t
   in
      sized-head ∷ sized-tail

{-
Given a list of individually sized expressions, we find the maximum size and cast every expression to that maximum size. In case the list is empty, the given default value is returned.
-}
unify-sizes : ∀ {B : Bounded}
  → Weaken B
  → Size
  → List (∃-Size[ i ] (B i))
  → ∃-Size[ max ] (List (B max))
unify-sizes _ ε [] = ε , []
unify-sizes w ε ((i , e) ∷ xs) =
  let (max-tail , tail) = unify-sizes w ε xs
   in i ⊔ˢ max-tail , prepend-sized w i max-tail e tail -- Why is there a warning highlight without a message here?

{-
Same as max-size⁺ but for non-empty list.
We can thus be sure that a maximum size exist and do not need a default value.
-}
unify-sizes⁺ : ∀ {B : Bounded} → Weaken B → List⁺ (∃-Size[ i ] (B i)) → ∃-Size[ max ] (List (B max))
unify-sizes⁺ L list@((i , _) ∷ _) = unify-sizes L i (toList list)
