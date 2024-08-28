# Binary Choice Calculus

## Module

```agda
open import Vatras.Framework.Definitions
module Vatras.Lang.2CC where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.Product using (_,_)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage
```

## Syntax

In the following we formalize the binary normal form for choice calculus.
We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.
A binary choice calculus expression is either an artifact `a -< es >-` (just as in [rose trees](../Framework/Variants.agda))
or a binary choice `D ⟨ l , r ⟩` between two sub-expressions `l` and `r`, where the dimension `D` gives the choice a name
to identify the choice upon configuration.
Dimensions `D` can be of any given type `Dimension : 𝔽`.
```agda
data 2CC (Dimension : 𝔽) : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (2CC Dimension i A) → 2CC Dimension (↑ i) A
   _⟨_,_⟩ : ∀ {i A} → Dimension → 2CC Dimension i A → 2CC Dimension i A → 2CC Dimension (↑ i) A
```

## Semantics

The semantics of binary normal form is essentially the same as for core choice calculus.
We define the semantics explicitly though because specializing the semantics to the binary case gives rise to simplifications and transformation rules.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also possible but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Configuration : (Dimension : 𝔽) → ℂ
Configuration Dimension = Dimension → Bool

⟦_⟧ : ∀ {i : Size} {Dimension : 𝔽} → 𝔼-Semantics (Rose ∞) (Configuration Dimension) (2CC Dimension i)
⟦ a -< cs >-  ⟧ c = a V.-< mapl (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ l , r ⟩ ⟧ c =
  if c D
  then ⟦ l ⟧ c
  else ⟦ r ⟧ c

2CCL : ∀ {i : Size} (Dimension : 𝔽) → VariabilityLanguage (Rose ∞)
2CCL {i} Dimension = ⟪ 2CC Dimension i , Configuration Dimension , ⟦_⟧ ⟫
```

In the following, we prove some interesting properties about binary choice calculus,
known from the respective papers.

```agda
module _ {Dimension : 𝔽} where
```

## Properties

Some transformation rules:
```agda
  open Data.List using ([_])
  open import Data.List.Properties using (map-∘; map-cong)
  open import Data.Nat using (ℕ)
  open import Data.Vec as Vec using (Vec; toList; zipWith)
  import Data.Vec.Properties as Vec
  import Vatras.Util.Vec as Vec

  open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)

  module Properties where
    open import Vatras.Framework.Relation.Expression (Rose ∞)

    module _ {A : 𝔸} where
      {-|
      Given a choice between two artifacts with the same atom 'a',
      we can factor out this atom 'a' outside of the choice because no matter
      how we configure the choice, the resulting expression will always have 'a'
      at the top.
      -}
      choice-factoring : ∀ {i} {D : Dimension} {a : atoms A} {n : ℕ}
        → (xs ys : Vec (2CC Dimension i A) n)
          ------------------------------------------------
        → 2CCL Dimension ⊢
              D ⟨ a -< toList xs >- , a -< toList ys >- ⟩
            ≣₁ a -< toList (zipWith (D ⟨_,_⟩) xs ys) >-
      choice-factoring {i} {D} {a} {n} xs ys c =
          ⟦ D ⟨ a -< toList xs >- , a -< toList ys >- ⟩ ⟧ c
        ≡⟨⟩
          (if c D then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
        ≡⟨ lemma (c D) ⟩
          a V.-< toList (zipWith (λ x y → if c D then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
        ≡⟨⟩
          a V.-< toList (zipWith (λ x y → ⟦ D ⟨ x , y ⟩ ⟧ c) xs ys) >-
        ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.map-zipWith (λ e → ⟦ e ⟧ c) (D ⟨_,_⟩) xs ys)) ⟨
          a V.-< toList (Vec.map (λ e → ⟦ e ⟧ c) (zipWith (D ⟨_,_⟩) xs ys)) >-
        ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) (zipWith (D ⟨_,_⟩) xs ys)) ⟩
          a V.-< mapl (λ e → ⟦ e ⟧ c) (toList (zipWith (D ⟨_,_⟩) xs ys)) >-
        ≡⟨⟩
          ⟦ a -< toList (zipWith (D ⟨_,_⟩) xs ys) >- ⟧ c
        ∎
        where
          open Eq.≡-Reasoning
          lemma : (b : Bool) →
              (if b then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
            ≡ a V.-< toList (zipWith (λ x y → if b then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
          lemma false =
              (if false then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
            ≡⟨⟩
              ⟦ a -< toList ys >- ⟧ c
            ≡⟨⟩
              a V.-< mapl (λ e → ⟦ e ⟧ c) (toList ys) >-
            ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) ys) ⟨
              a V.-< toList (Vec.map (λ y → ⟦ y ⟧ c) ys) >-
            ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.zipWith₂ (λ y → ⟦ y ⟧ c) xs ys)) ⟨
              a V.-< toList (zipWith (λ x y → ⟦ y ⟧ c) xs ys) >-
            ≡⟨⟩
              a V.-< toList (zipWith (λ x y → if false then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
            ∎
          lemma true =
              (if true then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
            ≡⟨⟩
              ⟦ a -< toList xs >- ⟧ c
            ≡⟨⟩
              a V.-< mapl (λ e → ⟦ e ⟧ c) (toList xs) >-
            ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) xs) ⟨
              a V.-< toList (Vec.map (λ x → ⟦ x ⟧ c) xs) >-
            ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.zipWith₁ (λ x → ⟦ x ⟧ c) xs ys)) ⟨
              a V.-< toList (zipWith (λ x y → ⟦ x ⟧ c) xs ys) >-
            ≡⟨⟩
              a V.-< toList (zipWith (λ x y → if true then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
            ∎

      {-|
      A choice between two equal alternatives is no choice.
      No matter how we configure the choice, the result stays the same.
      -}
      choice-idempotency : ∀ {D} {e : 2CC Dimension ∞ A}
          ---------------------------------
        → 2CCL Dimension ⊢ D ⟨ e , e ⟩ ≣₁ e
      choice-idempotency {D} {e} c with c D
      ... | false = refl
      ... | true  = refl

      {-|
      If the left alternative of a choice is semantically equivalent
      to another expression l′, we can replace the left alternative with l′.
      -}
      choice-l-congruence : ∀ {i : Size} {D : Dimension} {l l′ r : 2CC Dimension i A}
        → 2CCL Dimension ⊢ l ≣₁ l′
          ---------------------------------------
        → 2CCL Dimension ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l′ , r ⟩
      choice-l-congruence {D = D} l≣l′ c with c D
      ... | false = refl
      ... | true  = l≣l′ c

      {-|
      If the right alternative of a choice is semantically equivalent
      to another expression r′, we can replace the right alternative with r′.
      -}
      choice-r-congruence : ∀ {i : Size} {D : Dimension} {l r r′ : 2CC Dimension i A}
        → 2CCL Dimension ⊢ r ≣₁ r′
          ---------------------------------------
        → 2CCL Dimension ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l , r′ ⟩
      choice-r-congruence {D = D} r≣r′ c with c D
      ... | false = r≣r′ c
      ... | true  = refl
```

## Utility

```agda
  open Data.List using (concatMap) renaming (_++_ to _++l_)

  {-|
  Recursively, collect all dimensions used in a binary CC expression
  -}
  dims : ∀ {i : Size} {A : 𝔸} → 2CC Dimension i A → List Dimension
  dims (_ -< es >-)  = concatMap dims es
  dims (D ⟨ l , r ⟩) = D ∷ (dims l ++l dims r)
```

## Show

```agda
  open import Data.String as String using (String; _++_; intersperse)
  module Pretty (show-D : Dimension → String) where
    open import Vatras.Show.Lines

    show : ∀ {i} → 2CC Dimension i (String , String._≟_) → String
    show (a -< [] >-) = a
    show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
    show (D ⟨ l , r ⟩) = show-D D ++ "⟨" ++ (show l) ++ ", " ++ (show r) ++ "⟩"

    pretty : ∀ {i : Size} → 2CC Dimension i (String , String._≟_) → Lines
    pretty (a -< [] >-) = > a
    pretty (a -< es@(_ ∷ _) >-) = do
      > a ++ "-<"
      indent 2 do
        intersperseCommas (mapl pretty es)
      > ">-"
    pretty (D ⟨ l , r ⟩) = do
      > show-D D ++ "⟨"
      indent 2 do
        appendToLastLine "," (pretty l)
        pretty r
      > "⟩"
```
