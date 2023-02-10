{-# OPTIONS --sized-types #-}

{-
Module with functions for assisting Agda's type checker
when it comes to checking sized types.
Sometimes we need to help a lit with explicit type annotations
and safe casts.

This module is called juggling because sometimes Agda can magically convert between the two independent types Size and Size< which we can never do manually.
But sometimes Agda fails.
We can help it with some id functions that have the right type signature though.
-}
module Util.SizeJuggle where

-- to get ⊔ˢ type \lub\^s
-- remember to press ^ button twice!
open import Size using (Size; SizeUniv; Size<_; ↑_; _⊔ˢ_)

-- A size is smaller than itself + 1.
i<↑i : (i : Size) → Size< (↑ i)
i<↑i i = i

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

i<↑max : ∀ (i j : Size) → Size< (↑ (i ⊔ˢ j))
i<↑max i _ = i

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
