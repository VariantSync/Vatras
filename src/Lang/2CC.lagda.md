# Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Framework.Definitions
module Lang.2CC (Dimension : 𝔽) where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.Variants
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
open import Construct.Choices
```

## Syntax

In the following we formalize the binary normal forms for choice calculus. We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system. Our goal is to prove that every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.

```agda
data 2CC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (2CC i) A → 2CC (↑ i) A
   chc  : ∀ {i A} → VL2Choice.Syntax Dimension (2CC i) A → 2CC (↑ i) A

pattern _-<_>- a cs  = atom (a At.-< cs >-)
pattern _⟨_,_⟩ D l r = chc (D 2Choice.⟨ l , r ⟩)
```

## Semantics

The semantics of binary normal form is essentially the same as for n-ary choice calculus.
We define the semantics explicitly though because of two reasons:

1. Specializing the semantics to the binary case gives rise to further simplifications and transformation rules.
2. Defining binary semantics explicitly allows us to prove that a conversion from and to binary normal form is semantics preserving.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also possible but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Configuration : 𝕂
Configuration = 2Choice.Config Dimension

module Sem (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    2CCL : ∀ {i : Size} → VariabilityLanguage V
    2CCL {i} = ⟪ 2CC i , Configuration , ⟦_⟧ ⟫

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V Configuration (2CC i)
    ⟦ atom x ⟧ = PlainConstruct-Semantics Artifact-Construct mkArtifact 2CCL x
    ⟦ chc  x ⟧ = VL2Choice.Semantics V Dimension 2CCL id x
```

## Properties

Some transformation rules:
```agda
open import Util.AuxProofs using (if-idemp; if-cong)
open Data.List using ([_])
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; toList; zipWith)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

module Properties (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  open import Framework.Relation.Expression V
  open Sem V mkArtifact

  module _ {A : 𝔸} where
    ast-factoring : ∀ {i} {D : Dimension} {a : A} {n : ℕ}
      → (xs ys : Vec (2CC i A) n)
        -------------------------------------------------------------------------------------
      → 2CCL ⊢
            D ⟨ a -< toList xs >- , a -< toList ys >- ⟩
          ≣₁ a -< toList (zipWith (D ⟨_,_⟩) xs ys) >-
    ast-factoring xs ys c = {!!}

    choice-idempotency : ∀ {D} {e : 2CC ∞ A}  -- do not use ∞ here?
        ---------------------------
      → 2CCL ⊢ D ⟨ e , e ⟩ ≣₁ e
    choice-idempotency {D} {e} c with c D
    ... | false = refl
    ... | true  = refl

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
      with '2CC , ⟦_⟧ ⊢ e ≈ e′'
      -----------------------------------------------------------------------------------
      '2CC , ⟦_⟧ ⊢ Artifact a (toList (p -∷ e ∷- t)) ≈ Artifact a (toList (p -∷ e′ ∷- t))'
    where toList turns a zipper to a list and '-∷' and '∷-' denote the focus location behind the prefix and before the tail in the zipper.
    I expect proving this theorem to be quite boilerplaty but easy in theory:
    To show that both artifacts are semantically equivalent, we have to show that all the child nodes remain semantically equal.
    We know this by identity for all children in p and t.
    for e and e′, we know it per assumption.
    -}

    choice-l-congruence : ∀ {i : Size} {D : Dimension} {l l′ r : 2CC i A}
      → 2CCL ⊢ l ≣₁ l′
        ---------------------------------------
      → 2CCL ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l′ , r ⟩
    choice-l-congruence {D = D} l≣l′ c with c D
    ... | false = refl
    ... | true  = l≣l′ c

    choice-r-congruence : ∀ {i : Size} {D : Dimension} {l r r′ : 2CC i A}
      → 2CCL ⊢ r ≣₁ r′
        ---------------------------------------
      → 2CCL ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l , r′ ⟩
    choice-r-congruence {D = D} r≣r′ c with c D
    ... | false = r≣r′ c
    ... | true  = refl
```

## Semantic Preserving Transformations

```agda
module Redundancy (_==_ : Dimension → Dimension → Bool) where
  open import Data.Maybe using (Maybe; just; nothing)

  Scope : Set
  Scope = Dimension → Maybe Bool

  refine : Scope → Dimension → Bool → Scope
  refine scope D b D' = if D == D'
                        then just b
                        else scope D'

  eliminate-redundancy-in : ∀ {i : Size} {A : 𝔸} → Scope → 2CC i A → 2CC ∞ A
  eliminate-redundancy-in scope (a -< es >-) = a -< mapl (eliminate-redundancy-in scope) es >-
  eliminate-redundancy-in scope (D ⟨ l , r ⟩) with scope D
  ... | just true  = eliminate-redundancy-in scope l
  ... | just false = eliminate-redundancy-in scope r
  ... | nothing    = D ⟨ eliminate-redundancy-in (refine scope D true ) l
                       , eliminate-redundancy-in (refine scope D false) r
                       ⟩

  eliminate-redundancy : ∀ {i : Size} {A : 𝔸} → 2CC i A → 2CC ∞ A
  eliminate-redundancy = eliminate-redundancy-in (λ _ → nothing)

  open import Framework.Compiler using (LanguageCompiler)
  module _ (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
    open Sem V mkArtifact
    Redundancy-Elimination : LanguageCompiler 2CCL 2CCL
    Redundancy-Elimination = record
      { compile = eliminate-redundancy
      ; config-compiler = λ _ → record { to = id ; from = id }
      ; preserves = {!!}
      }
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → 2CC i A → List Dimension
dims (_ -< es >-) = concatMap dims es
dims (D ⟨ l , r ⟩) = D ∷ (dims l ++l dims r)
```

## Show

```agda
open import Data.String using (String; _++_; intersperse)
module Pretty (show-D : Dimension → String) where
  open import Show.Lines

  show : ∀ {i} → 2CC i String → String
  show (a -< [] >-) = a
  show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
  show (D ⟨ l , r ⟩) = show-D D ++ "⟨" ++ (show l) ++ ", " ++ (show r) ++ "⟩"


  pretty : ∀ {i : Size} → 2CC i String → Lines
  pretty (a -< [] >-) = > a
  pretty (a -< es@(_ ∷ _) >-) = do
    > a ++ "-<"
    indent 2 do
      lines (mapl pretty es)
    > ">-"
  pretty (D ⟨ l , r ⟩) = do
    > show-D D ++ "⟨"
    indent 2 do
      pretty l
      > ","
      pretty r
    > "⟩"
```