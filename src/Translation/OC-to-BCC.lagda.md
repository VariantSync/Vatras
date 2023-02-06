# Relating Option Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.OC-to-BCC where
```

## Imports

```agda
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapm)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; reverse; _++_; catMaybes) renaming (map to mapl)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product using (_×_; _,_)
open import Size using (Size; ↑_; ∞)

open import Lang.OC
     using ( OC; WFOC; Root; _❲_❳; Option; forgetWF; children-wf)
  renaming ( ⟦_⟧ to ⟦_⟧ₒ
           ; Artifact to Artifactₒ
           ; Configuration to Confₒ
           )
open import Lang.BCC
     using ( BCC; _⟨_,_⟩)
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Artifact to Artifact₂
           ; Configuration to Conf₂
           )
open import Lang.Annotation.Dimension using (Dimension; _==_)
open import Translation.Translation
     using ( Domain; Translation; TranslationResult )
open import Util.Existence using (∃-Size; _,_)
```

## Translation

What makes the translation hard?

1. Configuring Options globally: First my idea was, whenever we find an option, create a choice and evaluate the option to true for the left subtree and to false for the right subtree. Insight: This is already optimizing to avoid unnecessary nesting of duplicate choices. But nothing forces us to optimize _during_ a translation, more so because optimizations are only necessary if the input formula is un-optimized. Conclusion: Whenever we find an option, just translate it locally and continue (no global resolving of the option).
2. Reconstructing the tree:

```agda
-- PartialConf : Set
-- PartialConf = String → Maybe Bool

-- partialOC-Eval : ∀ {i : Size} {A : Domain} → PartialConf → OC i A → Maybe (OC i A)
-- partialOC-Eval c (Artifactₒ a es) = {!!}
-- partialOC-Eval c (O ❲ e ❳) with c O
-- ... | just b  = if b
--                 then partialOC-Eval c e
--                 else nothing
-- ... | nothing = mapm (λ e' → O ❲ e' ❳) (partialOC-Eval c e)

weaken-bound : ∀ {i : Size} {A : Domain} → OC i A → OC (↑ i) A
weaken-bound e = e

select-option : ∀ {i : Size} {A : Domain} → Option → OC i A → OC i A
select-option O (Artifactₒ a es) = Artifactₒ a (mapl (select-option O) es)
select-option O (O' ❲ e ❳) = let e' = select-option O e in
                             if O == O'
                             then weaken-bound e'
                             else O' ❲ e' ❳

import Relation.Binary.PropositionalEquality as Eq
open Eq using (inspect)

select-option-wf : ∀ {i : Size} {A : Domain} → Option → WFOC i A → WFOC i A
select-option-wf O (Root a es) with select-option O (Artifactₒ a es) | inspect (select-option O) (Artifactₒ a es)
... | Artifactₒ a' es' | _ = Root a' es'

deselect-option : ∀ {i : Size} {A : Domain} → Option → OC i A → Maybe (OC i A)
deselect-option O (Artifactₒ a es) = just (Artifactₒ a (catMaybes (mapl (deselect-option O) es)))
deselect-option O (O' ❲ e ❳) = if O == O'
                               then nothing
                               else mapm (λ x → O' ❲ x ❳) (deselect-option O e)

deselect-option-wf : ∀ {i : Size} {A : Domain} → Option → WFOC i A → WFOC i A
deselect-option-wf O (Root a es) with deselect-option O (Artifactₒ a es) | inspect (deselect-option O) (Artifactₒ a es)
... | just (Artifactₒ a' es') | _ = Root a' es'

data ReversedList (A : Set) : Set where
  [] : ReversedList A
  _∷_ : ReversedList A → A → ReversedList A

maprl : ∀ {A B : Set} → (f : A → B) → ReversedList A → ReversedList B
maprl f [] = []
maprl f (xs ∷ x) = maprl f xs ∷ f x

unreverse : ∀ {A : Set} → ReversedList A → List A
unreverse [] = []
unreverse (xs ∷ x) = unreverse xs ++ (x ∷ [])

open import Effect.Functor using (RawFunctor)
--open import Effect.Applicative using (RawApplicative; pure)
open import Effect.Monad using (RawMonad)

-- Import state monad
open import Effect.Monad.State
  using (State; RawMonadState; runState; execState; evalState)
  renaming (functor to state-functor;
--            applicative to state-applicative;
            monad to state-monad;
            monadState to state-monad-specifics)

record ListZipper (A : Set) : Set where
   constructor _⚈_ -- \ci (option 3 on page 3)
   field
     left  : ReversedList A
     right : List A
open ListZipper public
infix 4 _⚈_

maplz : ∀ {A B : Set} → (f : A → B) → ListZipper A → ListZipper B
maplz f z = record
  { left  = maprl f (left  z)
  ; right = mapl  f (right z)
  }

-- focus of zipper as at head of right
-- focus : ∀ {A : Set} → ListZipper A → Maybe A
-- focus record { right = []       } = nothing
-- focus record { right = (r ∷ rs) } = just r

fromList : ∀ {A : Set} → List A → ListZipper A
fromList l = record
  { left  = []
  ; right = l
  }

toList : ∀ {A : Set} → ListZipper A → List A
toList lz = unreverse (left lz) ++ (right lz)

goRight : ∀ {A : Set} → ListZipper A → ListZipper A
goRight zipper with (right zipper)
... | []       = zipper
... | (r ∷ rs) = record
               { left  = left zipper ∷ r
               ; right = rs
               }

-- data TFocus (A : Domain) : Set where
--   _⊣  : A → TFocus A -- \-|
--   _⊸_ : A → TFocus A → TFocus A -- \-o

record TZipper (i : Size) (A : Domain) : Set where
  constructor _◀_ --\T
  field
    context : List⁺ A
    focus   : ListZipper (OC i A)

-- {-# TERMINATING #-}
-- travList : ∀ {i : Size} {A : Domain} → TZipper A → ListZipper (OC i A) → BCC i A
-- travList tz lz@(record { right = []         }) = {!!}
-- travList tz lz@(record { right = focus ∷ rs }) with focus
-- ... | Artifactₒ a es = travList tz (goRight lz)
-- ... | O ❲ es ❳ = {!!}
{-# TERMINATING #-}
OCtoBCC' : ∀ {i : Size} {A : Domain} → TZipper i A → BCC ∞ A
OCtoBCC' ((a ∷ p) ◀    (left ⚈ [])) = {!!} -- return (Artifact₂ a (unreverse left))
-- skip artifacts. Should we recursively translate 
OCtoBCC' ((a ∷ p) ◀    (left ⚈ foc@(Artifactₒ b es) ∷ rs)) =
  -- TODO: Translate foc and remember that we did so at the type level! This likely also simplifies the option case below. It would also allow us to implement the first case where we finished traversing the children list because then we could return "Artifact₂ a (unrevers left)".
  OCtoBCC' ((a ∷ p) ◀ (left ∷ foc ⚈ rs))
OCtoBCC' ((a ∷ p) ◀ es@(left ⚈ O ❲ e ❳ ∷ rs)) = --{!!}
  -- TODO: Currently we forget our position in the zipper and redo some computation when we evaluated the option. In particular, we re-iterate "left".
  -- Can we build this translation, such that everything in "left" is already translated? This would potentially also help with termination checking.
   let -- 1. We know that we are a child of "Artifact a es", so we are in a well-formed sub-expression.
       subtree = Root a (toList es)
       -- 2. We are going to construct an alternative for the option O we found. When we go left, we select O, otherwise we deselect O. We obtain a well-formed OC expression of which we know that it's root is still "a". So we can ignore "a" and obtain the partially configured children.
       ls = children-wf (  select-option-wf O subtree)
       rs = children-wf (deselect-option-wf O subtree)
       -- 3. Recursively translate all remaining terms. We know that a is still at the root of our expression.
       l  = OCtoBCC' ((a ∷ p) ◀ fromList ls)
       r  = OCtoBCC' ((a ∷ p) ◀ fromList rs)
   in
      -- 4. Build the choice.
      O ⟨ l , r ⟩

-- Todo: remove temp ∞
OCtoBCC : ∀ {i : Size} {A : Domain} → WFOC i A → ∃-Size[ j ] (BCC j A)
OCtoBCC (Root a es) = ∞ , OCtoBCC' ((a ∷ []) ◀ fromList es)

translate : ∀ {i : Size} {A : Domain} → WFOC i A → TranslationResult A BCC Confₒ Conf₂
translate oc =
  let j , bcc = OCtoBCC oc in
  record
  { size = j
  ; expr = bcc
  ; conf = {!!}
  ; fnoc = {!!}
  }

OC→BCC : Translation WFOC BCC Confₒ Conf₂
OC→BCC = record
  { sem₁ = ⟦_⟧ₒ
  ; sem₂ = ⟦_⟧₂
  ; translate = translate
  }
```

