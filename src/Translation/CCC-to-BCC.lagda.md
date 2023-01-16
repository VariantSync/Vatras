# Relating Core Choice Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.CCC-to-BCC where
```

## Imports

```agda

```

## Translation

To convert choice calculus to binary normal form, we have to convert n-ary choices to binary choices.
We can do so by recursively nesting alternatives beyond the second in nested binary decisions.
This translation follows the similar observations for if-statements that an `elseif` expression is equivalent to an `else` branch with a nested `if`:

      if x
        then a
      elif y
        then b
      else
        c

    ≡ if x
        then a
      else
        if y
          then b
        else
          c

One of the key challenges for this translations is to introduce correct new conditions (i.e., dimensions) for the nested choices.
Here, this means, we have to generate new choices, and thus new dimensions.
In the above example, this is not necessary because every branch already has a condition, but in choice calculus, every alternative is just identified by an index below a dimension.
So for example, the first if-elif-else chain would be expressed as `D⟨a, b, c⟩`, where `D` somehow reflects the conditions `x` and `y`.
So to translate this chain to binary, we have to nest every alternatives beyond the first, such that `D⟨a, b, c⟩` becomes `D⟨a, E⟨b, c⟩⟩`, where `E` is a new new name that corresponds to `y` in the second if-else-if-else chain above.
When generating a new name for a new dimension, we have to assume that it does not exist yet or otherwise, we cannot preserve semantics.
For example, when generating names by appending tick marks, we may get `toCC₂ (D⟨a,b,D'⟨c, d⟩⟩) ≡ D⟨a, D'⟨b, D'⟨c, d⟩⟩⟩` which has different semantics than the input.

We identified two possible ways to ensure that new generated names do not collide with existing dimension names:

1. Bake uniqueness into the type-level by using a different type for dimension in the output expression: Values of the new type would ensure that these values were never part of the original input expression. However, this is very intrusive into the language design and introduces complexity for all matters other than conversion to binary normal form. It also obfuscates the language design for an easier solution to this particular problem. That is why we choose the second alternative below.
2. Ensure that any new dimension name does not collide (as shown in the example above). Collision can either occur with names from the input formula or in the output formula. When generating a new name, we can only guarantee that it does not collide with another name in the input formula by comparing it to every name in the input formula. This is an intricate process, vastly complicating proofs. Another strategy would be to ensure that any generated name in the output formula collides exactly with those names in the output formula for which both respective dimensions in the input formula collided. For example, when transforming `D⟨D⟨x, y, z⟩, A⟨u, v, w⟩, n⟩`, we have to introduce new dimensions for `D` and `A` because these have arity greater 2. For both occurences of `D`, the generated dimension has to have the same name to ensure choice synchronization (see Erics PhD thesis). And these two names must collide in the output but must not collide with any other name. For example, `D⟨D⟨x, D'⟨y, z⟩⟩, D'⟨A⟨u, A'⟨v, w⟩⟩, n⟩⟩` would be valid but the generated name `D'` can still collide with names for the input formula.

To prevent collisions of names, we (1) rename every dimension in the input in a consistent way and (2) also generate new names following this way. This allows us to ensure that generated names do not collide with other existing names.
The idea is to append an index to every dimension that indicates the tag that had to be chosen in the input formula to pick that choice's left alternative.

Example: `D⟨x, y, z, w⟩ ↦ D.0⟨x, D.1⟨y, D.2⟨z, w⟩⟩⟩`

Definition:
```agda
open import Data.Nat.Show renaming (show to show-nat)

indexedDim : Dimension → ℕ → Dimension
indexedDim D n = D ++ "." ++ (show-nat n) -- Do not simplify for n ≡ᵇ zero! I know names like A.0 are ugly if we can avoid them but dropping the .0 where possible can cause name collisions in the output formula!
```

Here is an informal proof that using `indexedDim` to rename every dimension does not cause unintended choice synchronizations:

    Every dimension D in the input formula is renamed to (D ++ ".0").
    Thus every dimension is manipulated equally and thus, this transformation is a true renaming.

    Removal of dimensions occurs only for unary choices and cannot invalidate uniqueness of names anyway.

    New dimensions are introduced only to unroll a dimension from the input formula.
    This means, each generated dimension G is associated to exactly one dimension D from the input formula.
    The name of G is (D ++ "." ++ suc n) for an n : ℕ.
    The name of G is new because of proof by contradiction:
      Assume the name of G is not new (i.e., collides).
      This means there is dimension A in the output formula with the same name as G
      but A was associated to another dimension in the input formula.
      The name of A is of the form (I ++ "." m) for an m : ℕ and a dimension I from the input formula.
      Because A has the same name as G, we know that I = D and suc n = m.
      Thus, both A and G originate from the same dimension in the input formula.
      This contradicts our assumption that G collided.

To prove that a translation from choice calculus to binary normal form is semantics-preserving, we have to show that both, the input as well as the output expression, describe the same set of variants (just as we did earlier for the inverse translation).
As we will see later, this requires us to not only translate an expression from n-ary to binary form, but also configurations.
Our implementation of the translation thus takes an n-ary choice calculus expression as input and yields two results: (1) a converter that can translate configurations for the input formula to configurations for the output formula and vice versa, and (2) the expression in binary normal form.
To define the configuration converter, we use the state monad that keeps track of our current progress of translating configurations.

We thus first import the necessary definitions from the standard library:
```agda
-- Import general functor and monad operations.
open import Effect.Functor using (RawFunctor)
--open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

-- Import state monad
open import Effect.Monad.State
  using (State; RawMonadState; runState)
  renaming (functor to state-functor;
            applicative to state-applicative;
            monad to state-monad;
            monadState to state-monad-specifics)

-- Import traversable for lists
import Data.List.Effectful
open Data.List.Effectful.TraversableA using (sequenceA) renaming (mapA to traverse)
```

To convert configurations for the input formula to configurations for the output formula and vice versa, we introduce the following record.
We use this record as the state during our translation.
```agda
-- resembles a specialized version of _⇔_ in the plfa book
record ConfigurationConverter : Set where
  field
    nary→binary : Configuration  → Configuration₂
    binary→nary : Configuration₂ → Configuration
open ConfigurationConverter

-- Default configuration converter that always goes left.
-- We use it as a base case when we have no further information.
unknownConfigurationConverter : ConfigurationConverter
unknownConfigurationConverter = record
  { nary→binary = λ _ _ → true
  ; binary→nary = λ _ _ → 0
  }

-- The state we are going to use during the translation from n-ary to binary choice calculus.
-- We keep track of the current configuration converter and update it when necessary.
TranslationState : Set → Set
TranslationState = State ConfigurationConverter
```

We can now define our translation function `toCC₂`.
Sadly, we cannot prove it terminating yet.
The problem is that the alternatives of a choice are a list, and this list is converted to a recursive nesting structure.
For example, `D ⟨ a , b , c , d ⟩` becomes `D.0 ⟨ a , D.1 ⟨ b , D.2 ⟨ c , d ⟩₂ ⟩₂ ⟩₂`.
Hence, the number of children of a CC expression determines the nesting depth of the resulting binary expression.
Since we have no guarantees on the number of children (i.e., no bound / estimate), we cannot make any guarantees on the maximum depth of the resulting expression.
Moreover, because a children list thus could be infinite, also the resulting expression could be infinite.
Thus, this function might indeed not terminate.
To solve this, we would have to introduce yet another bound to n-ary choice calculus: an upper bound for the number of children of each node.
We should later decide if this extra boilerplate is worth it or not.

```agda
-- helper function to keep track of state
{-# TERMINATING #-}
toCC₂' : ∀ {i : Size} {A : Set} → CC i A → TranslationState (CC₂ ∞ A)

-- actural translation function
toCC₂ : ∀ {i : Size} {A : Set} → CC i A → ConfigurationConverter × CC₂ ∞ A
toCC₂ cc = runState (toCC₂' cc) unknownConfigurationConverter

{- |
Unroll choices by recursively nesting any alternatives beyond the first.
Example: D ⟨ u ∷ v ∷ w ∷ [] ⟩ → D.0 ⟨ u, D.1 ⟨ v , w ⟩₂ ⟩₂
-}

toCC₂'-choice-unroll : ∀ {i : Size} {A : Set}
  → Dimension      -- initial dimension in input formula that we translate (D in the example above).
  → ℕ             -- Current alternative of the given dimension we are translating. zero is left-most alternative (pointing to u in the example above).
  → List⁺ (CC i A) -- remaining alternatives of the choice to unroll. We let this shrink recursively.
  → TranslationState (CC₂ ∞ A)

-- Leave artifact structures unchanged but recursively translate all children.
-- Translating all children yields a list of states which we evaluate in sequence.
toCC₂' (Artifact a es) =
  let open RawFunctor state-functor in
  Artifact₂ a <$> (traverse state-applicative toCC₂' es)
toCC₂' (D ⟨ es ⟩) = toCC₂'-choice-unroll D zero es

open import Data.Nat renaming (_≡ᵇ_ to _nat-≡ᵇ_)
open import Util.Util using (empty?)

update-configuration-converter :
    ConfigurationConverter
  → Dimension  -- corresponding dimension in the input n-ary expression
  → ℕ         -- current nesting depth (see toCC₂'-choice-unroll)
  → Dimension  -- name of the corresponding dimension in the output binary expression
  → Bool       -- True iff the currently inspected choice is binary.
  → ConfigurationConverter
update-configuration-converter conf-converter D n D' binary? =
    let n→b = nary→binary conf-converter
        b→n = binary→nary conf-converter
    in record
      -- Given an n-ary configuration cₙ for the input formula, we want to find the value of a given dimension in the binary output formula
      { nary→binary = (λ {cₙ queried-output-dimension →
          -- If the queried dimension was translated from our currently translated dimension D.
          if (queried-output-dimension == D')
          -- If the selection made in the input formula did select the left alternative of our choice
          -- then also pick it in the binary output formula. Otherwise, do not pick it.
          -- In case cₙ D <ᵇ n, the result does not matter. Then, an alternative above this choice was already chosen
          -- (and we are within an else branch). So it does not matter what we pick here. Could be true, false, or n→b cₙ queried-output-dimension.
          -- In case cₙ D >ᵇ n, the result has to be false because the alternative that has to be picked is on the right, which is only checked if we do not go left here.
          then (cₙ D nat-≡ᵇ n)
          -- If not, ask our existing configuration translation knowledge.
          else (n→b cₙ queried-output-dimension)
          })
      -- Given a binary configuration c₂ for the output formula, we want to find the value of a queried dimension in the n-ary input formula.
      ; binary→nary = (λ {c₂ queried-input-dimension →
          let recursive-result = b→n c₂ queried-input-dimension in
          -- If the queried dimension is the dimension we currently translate.
          if (queried-input-dimension == D)
          then (if (c₂ D')       -- If the binary configuration has chosen the left alternative of the nested binary dimension
                then n           -- ... then that is the alternative we have to pick in the input formula.
                else (if binary? -- ... if not, we check if the current choice is already binary.
                      then suc n            -- If it is, we pick the right alternative.
                      else recursive-result -- Otherwise, we check further nested branches recursively.
                      )
                )
          else recursive-result
          })
      }

-- Use the idempotency rule D⟨e⟩≈e to unwrap unary choices.
-- This is where recursion stops.
toCC₂'-choice-unroll D n (e₁ ∷ []) = toCC₂' e₁
-- For n-ary choices with n > 1, convert the head and recursively convert the tail.
toCC₂'-choice-unroll D n (e₁ ∷ e₂ ∷ es) =
  let open RawMonad state-monad
      open RawMonadState state-monad-specifics
  in do
    let D' = indexedDim D n

    -- translation of the formula
    cc₂-e₁   ← toCC₂' e₁
    cc₂-tail ← toCC₂'-choice-unroll D (suc n) (e₂ ∷ es)

    -- translation of configurations
    -- The tail length check is actually a recursion end that checks if we are left with a binary choice.
    -- So we might want to introduce a pattern matching case for binary choices instead of doing this runtime-check here.
    -- However, this abstraction causes more boilerplate than it simplifies.
    -- Let's see how much more complicated the proofs become.
    conf-converter ← get
    put (update-configuration-converter conf-converter D n D' (empty? es))

    pure (D' ⟨ cc₂-e₁ , cc₂-tail ⟩₂)
```

Now we prove that conversion to binary normal form is semantics preserving (i.e., the set of described variants is the same).
```
{-
CC→CC₂-left : ∀ {i : Size} {A : Set} {e : CC i A}
    -------------
  → proj₂ (toCC₂ e) ₂⊂̌ₙ e

CC→CC₂-right : ∀ {i : Size} {A : Set} {e : CC i A}
    -------------
  → e ₙ⊂̌₂ proj₂ (toCC₂ e)

CC→CC₂ : ∀ {i : Size} {A : Set} {e : CC i A}
    ----------
  → proj₂ (toCC₂ e) ₂≚ₙ e
CC→CC₂ {i} {A} {e} =
    CC→CC₂-left  {i} {A} {e}
  , CC→CC₂-right {i} {A} {e} -}
```

#### Proof of the left side

```agda
{-
-- Every variant described by the translated expression is also described by the initial expression.
CC→CC₂-left' : ∀ {i : Size} {A : Set}
  → ∀ (e : CC i A)
  → ∀ (c₂ : Configuration₂)
    ------------------------------------------------------------------
  → ⟦ proj₂ (toCC₂ e) ⟧₂ c₂ ≡ ⟦ e ⟧ (binary→nary (proj₁ (toCC₂ e)) c₂)

CC→CC₂-left' (Artifact a []) c₂ = refl
CC→CC₂-left' e@(Artifact a es@(_ ∷ _)) c₂ =
  let open RawFunctor state-functor
      c = binary→nary (proj₁ (toCC₂ e)) c₂
  in
  begin
    ⟦ proj₂ (toCC₂ e) ⟧₂ c₂
  ≡⟨⟩
    ⟦ proj₂ (runState (Artifact₂ a <$> (traverse state-applicative toCC₂' es)) unknownConfigurationConverter) ⟧₂ c₂
  ≡⟨⟩
    Artifactᵥ a (mapl (flip ⟦_⟧₂ c₂) (proj₂ (runState (sequenceA state-applicative (mapl toCC₂' es)) unknownConfigurationConverter)))
  -- TODO: Somehow apply the induction hypothesis below the sequenceA below the runState below the mapl below the Artifactᵥ
  ≡⟨ Eq.cong (λ m → Artifactᵥ a m) {!!} ⟩
    Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
  ≡⟨⟩
    ⟦ e ⟧ c
  ∎
CC→CC₂-left' (D ⟨ e ∷ [] ⟩) c₂ =
  let conf = binary→nary (proj₁ (toCC₂ (D ⟨ e ∷ [] ⟩))) c₂ in
  ⟦ proj₂ (toCC₂ (D ⟨ e ∷ [] ⟩)) ⟧₂ c₂ ≡⟨⟩
  ⟦ proj₂ (toCC₂ e            ) ⟧₂ c₂ ≡⟨ CC→CC₂-left' e c₂ ⟩
  ⟦ e           ⟧ conf                ≡⟨⟩
  ⟦ D ⟨ e ∷ [] ⟩ ⟧ conf                ∎
CC→CC₂-left' e@(D ⟨ es@(_ ∷ _ ∷ _) ⟩) c₂ =
  let conf = binary→nary (proj₁ (toCC₂ e)) c₂
      e₂ = proj₂ (toCC₂ e)
  in
  begin
    ⟦ proj₂ (toCC₂ e) ⟧₂ c₂
  --≡⟨ {!!} ⟩
  --  ⟦ if (c₂ D) then {!!} else {!!} ⟧₂ c₂
  ≡⟨ {!!} ⟩
    ⟦ choice-elimination (conf D) es ⟧ conf
  ≡⟨⟩
    ⟦ e ⟧ conf
  ∎

CC→CC₂-left {i} {A} {e} c₂ =
  let conf-trans , cc₂ = toCC₂ e in
  binary→nary conf-trans c₂ , CC→CC₂-left' e c₂ -}
```

#### Proof of the right side

```agda
-- Every variant described by an n-ary CC expression, is also described by its translation to binray CC.
{-
CC→CC₂-right' : ∀ {i : Size} {A : Set}
  → ∀ (e : CC i A)
  → ∀ (c : Configuration)
    -----------------------------------------------------------------
  → ⟦ proj₂ (toCC₂ e) ⟧₂ (nary→binary (proj₁ (toCC₂ e)) c) ≡  ⟦ e ⟧ c

CC→CC₂-right' (Artifact a []) c = refl
CC→CC₂-right' (Artifact a es@(_ ∷ _)) c = {!!}
CC→CC₂-right' (D ⟨ e ∷ [] ⟩) c = CC→CC₂-right' e c -- just apply the induction hypothesis on the only mandatory alternative
CC→CC₂-right' (D ⟨ es@(_ ∷ _ ∷ _) ⟩) c = {!!}

CC→CC₂-right {i} {A} {e} c =
  let conf-trans , cc₂ = toCC₂ e in
  nary→binary conf-trans c , CC→CC₂-right' e c -}
```
