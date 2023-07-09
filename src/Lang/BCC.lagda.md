# Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.BCC where
```

## Imports

```agda
-- stdlib
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Function
  using (flip; id)
open import Size
  using (Size; ∞; ↑_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- own modules
open import Framework.Annotation.Name using (Dimension)
open import Framework.Definitions hiding ([_])
open import Relations.Semantic using (_⊢_≣_)
```

## Syntax

In the following we formalize the binary normal forms for choice calculus. We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system. Our goal is to prove that every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.

```agda
data BCC : 𝕃 where
  Artifact : Artifactˡ BCC
  _⟨_,_⟩ : ∀ {i : Size} {A : 𝔸} →
    Dimension → BCC i A → BCC i A → BCC (↑ i) A
```

## Semantics

The semantics of binary normal form is essentially the same as for n-ary choice calculus.
We define the semantics explicitly though because of two reasons:

1. Specializing the semantics to the binary case gives rise to further simplifications and transformation rules.
2. Defining binary semantics explicitly allows us to prove that a conversion from and to binary normal form is semantics preserving.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also ok but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Tag : Set
Tag = Bool

left  = true
right = false

Configuration : ℂ
Configuration = Dimension → Tag

{-
This is the semantics for choice calculus as defined in
"Projectional Editing of Variational Software, Walkingshaw and Ostermann, GPCE'14"
with the minor simplification of using booleans instead of selectors for dimensions.
-}
-- ⟦_⟧ : ∀ {i : Size} {A : 𝔸} → BCC i A → Configuration → Variant i A
⟦_⟧ : Semantics BCC Configuration
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ l , r ⟩ ⟧ c = ⟦ if (c D) then l else r ⟧ c

BCCL : VariabilityLanguage
BCCL = record
  { expression    = BCC
  ; configuration = Configuration
  ; semantics     = ⟦_⟧
  }
```

## Properties

Some transformation rules from the GPCE'14 paper:
```agda
open import Util.AuxProofs using (if-idemp; if-cong)
open Data.List using ([_])
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; toList; zipWith)

-- This is a special case of ast-factoring where artifacts have only one child.
-- As soon as 'ast-factoring' is proven, we can reformulate the proof for this theorem
-- to just apply ast-factoring.
ast-factoring-1 : ∀ {A D} {a : A} {x y : BCC ∞ A} -- do not use ∞ here?
    ---------------------------------------------------------------------------------
  → BCCL ⊢ D ⟨ Artifact a [ x ] , Artifact a [ y ] ⟩ ≣ Artifact a [ D ⟨ x , y ⟩ ]
ast-factoring-1  {_} {D} {a} {x} {y} c =
  begin
    ⟦ D ⟨ Artifact a [ x ] , Artifact a [ y ] ⟩ ⟧ c
  ≡⟨⟩
    ⟦ if (c D) then (Artifact a [ x ]) else (Artifact a [ y ] ) ⟧ c
  ≡⟨ Eq.cong (flip ⟦_⟧ c) (if-cong (c D) (λ {v → Artifact a [ v ]}) ) ⟩
    ⟦ Artifact a [ if (c D) then x else y ] ⟧ c
  ≡⟨⟩
    ⟦ Artifact a [ D ⟨ x , y ⟩ ] ⟧ c
  ∎

ast-factoring : ∀ {i : Size} {A : 𝔸} {D : Dimension} {a : A} {n : ℕ}
  → (xs ys : Vec (BCC i A) n)
    -------------------------------------------------------------------------------------
  → BCCL ⊢
        D ⟨ Artifact a (toList xs) , Artifact a (toList ys) ⟩
      ≣ Artifact a (toList (zipWith (D ⟨_,_⟩) xs ys))
ast-factoring = {!!}

choice-idempotency : ∀ {A D} {e : BCC ∞ A}  -- do not use ∞ here?
    ---------------------------
  → BCCL ⊢ D ⟨ e , e ⟩ ≣ e
choice-idempotency {A} {D} {e} c =
  ⟦ D ⟨ e , e ⟩ ⟧ c             ≡⟨⟩
  ⟦ if (c D) then e else e ⟧ c  ≡⟨ Eq.cong (flip ⟦_⟧ c) (if-idemp (c D)) ⟩
  ⟦ e ⟧ c                       ∎

{-
TODO: Formulate choice-domination.
We cannot do this currently because we only cover total configurations so far.
We have to implement choice-elimination as an extra function first.
-}

{-
TODO: Formulate AST-congruence.
This is tricky because it ranges over any sub-expression below an artifact (i.e., an arbitrary element in that list).
Maybe using a zipper on lists (i.e., a list where we can focus any element except for just the head) is what we want here.
Then we could say:
∀ expressions 'e' and 'e′',
  prefix 'p', and tail 't'
  with 'BCC , ⟦_⟧ ⊢ e ≈ e′'
  -----------------------------------------------------------------------------------
  'BCC , ⟦_⟧ ⊢ Artifact a (toList (p -∷ e ∷- t)) ≈ Artifact a (toList (p -∷ e′ ∷- t))'
where toList turns a zipper to a list and '-∷' and '∷-' denote the focus location behind the prefix and before the tail in the zipper.
I expect proving this theorem to be quite boilerplaty but easy in theory:
To show that both artifacts are semantically equivalent, we have to show that all the child nodes remain semantically equal.
We know this by identity for all children in p and t.
for e and e′, we know it per assumption.
-}

choice-l-congruence : ∀ {i j k : Size} {A : 𝔸} {D : Dimension} {eₗ eₗ′ eᵣ : BCC i A}
  → BCCL ⊢ eₗ ≣ eₗ′
    ---------------------------------------
  → BCCL ⊢ D ⟨ eₗ , eᵣ ⟩ ≣ D ⟨ eₗ′ , eᵣ ⟩
choice-l-congruence eₗ≡eₗ′ = {!!}

choice-r-congruence : ∀ {i j k : Size} {A : 𝔸} {D : Dimension} {eₗ eᵣ eᵣ′ : BCC i A}
  → BCCL ⊢ eᵣ ≣ eᵣ′
    ---------------------------------------
  → BCCL ⊢ D ⟨ eₗ , eᵣ ⟩ ≣ D ⟨ eₗ , eᵣ′ ⟩
choice-r-congruence eₗ≡eₗ′ = {!!}
```

## Semantic Preserving Transformations

```agda
open Framework.Annotation.Name using (_==_)
open import Data.Maybe using (Maybe; just; nothing)
open import Translation.Translation using (EndoTranslation)

Scope : Set
Scope = Dimension → Maybe Bool

refine : Scope → Dimension → Bool → Scope
refine scope D b D' = if D == D'
                      then just b
                      else scope D'

eliminate-redundancy-in : ∀ {i : Size} {A : 𝔸} → Scope → BCC i A → BCC i A
eliminate-redundancy-in scope (Artifact a es) = Artifact a (mapl (eliminate-redundancy-in scope) es)
eliminate-redundancy-in scope (D ⟨ l , r ⟩) with scope D
... | just true  = eliminate-redundancy-in scope l
... | just false = eliminate-redundancy-in scope r
... | nothing    = D ⟨ eliminate-redundancy-in (refine scope D true) l
                     , eliminate-redundancy-in (refine scope D false) r
                     ⟩

eliminate-redundancy : ∀ {i : Size} {A : 𝔸} → BCC i A → BCC i A
eliminate-redundancy = eliminate-redundancy-in (λ _ → nothing)

Redundancy-Elimination : EndoTranslation BCCL
Redundancy-Elimination e = record
  { expr = eliminate-redundancy e
  ; conf = id
  ; fnoc = id
  }
```

## Sized Helper Functions

```agda
open import Util.SizeJuggle using (Bounded; Weaken; to-larger; to-max)

-- todo: move these boundes definition to BCC file
BCC-is-bounded : ∀ 𝔸 → Bounded
BCC-is-bounded A i = BCC i A

BCC-is-weakenable : ∀ {A : 𝔸} → Weaken (BCC-is-bounded A)
to-larger BCC-is-weakenable _ _ e = e
to-max    BCC-is-weakenable _ _ e = e
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → BCC i A → List Dimension
dims (Artifact _ es) = concatMap dims es
dims (D ⟨ l , r ⟩) = D ∷ (dims l ++l dims r)
```

## Show

```agda
open import Data.String using (String; _++_; intersperse)

show : ∀ {i : Size} → BCC i String → String
show (Artifact a []) = a
show (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
show (D ⟨ l , r ⟩) = D ++ "⟨" ++ (show l) ++ ", " ++ (show r) ++ "⟩"

open import Show.Lines

pretty : ∀ {i : Size} → BCC i String → Lines
pretty (Artifact a []) = > a
pretty (Artifact a es@(_ ∷ _)) = do
  > a ++ "-<"
  indent 2 do
    lines (mapl pretty es)
  > ">-"
pretty (D ⟨ l , r ⟩) = do
  > D ++ "⟨"
  indent 2 do
    pretty l
    > ","
    pretty r
  > "⟩"
```
