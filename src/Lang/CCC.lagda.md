# Core Choice Calculus

## Module

```agda
open import Framework.Definitions
module Lang.CCC where
```

## Imports
```agda
-- -- Imports from Standard Library
open import Data.List
  using (List; []; _∷_; foldl; map)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to map⁺)
open import Data.Product
  using (_,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open import Data.Nat using (ℕ)

open import Function using (id; _∘_; _$_)
open import Size using (Size; ↑_; ∞)

open import Framework.Variants as V using (Rose; VariantEncoder; Variant-is-VL)
open import Framework.VariabilityLanguage
open import Util.List using (find-or-last)

open import Data.EqIndexedSet as ISet
```

## Syntax

```agda
data CCC (Dimension : 𝔽) : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (CCC Dimension i A) → CCC Dimension (↑ i) A
   _⟨_⟩ : ∀ {i A} → Dimension → List⁺ (CCC Dimension i A) → CCC Dimension (↑ i) A
```

## Semantics

Choice calculus has denotational semantics.
Semantics for choice calculus can be defined in different ways.
- As a set of pairs `Configuration × Variant`
- As a configuration function `Configuration → Variant` that generates variants from configurations.

The second definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by tags:
```agda
Configuration : (Dimension : 𝔽) → ℂ
Configuration Dimension = Dimension → ℕ
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., the number of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to avoid complex error handling and we cannot easily define a configuration to only produce tags within ranges.
```agda
⟦_⟧ : ∀ {i : Size} {Dimension : 𝔽} → 𝔼-Semantics (Rose ∞) (Configuration Dimension) (CCC Dimension i)
⟦ a -< cs >- ⟧ c = a V.-< map (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ cs ⟩   ⟧ c = ⟦ find-or-last (c D) cs ⟧ c

CCCL : ∀ {i : Size} (Dimension : 𝔽) → VariabilityLanguage (Rose ∞)
CCCL {i} Dimension = ⟪ CCC Dimension i , Configuration Dimension , ⟦_⟧ ⟫
```

```agda
module _ {Dimension : 𝔽} where
```

## Properties

Some transformation rules
```agda
  module Properties where
    open import Framework.Relation.Expression (Rose ∞)

    module _ {A : 𝔸} where
      -- unary choices are mandatory
      D⟨e⟩≣e : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          -----------------------------
        → CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≣₁ e
      D⟨e⟩≣e _ = refl

      -- other way to prove the above via variant-equivalence

      D⟨e⟩⊆e : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          -------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≤ e
      D⟨e⟩⊆e c = c , refl

      e⊆D⟨e⟩ : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          -------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ e ≤ D ⟨ e ∷ [] ⟩
      e⊆D⟨e⟩ c = c , refl

      D⟨e⟩≣e' : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          ------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≣ e
      D⟨e⟩≣e' {e} {D} = D⟨e⟩⊆e {e} {D} , e⊆D⟨e⟩ {e} {D}
```

## Completeness

Proof in progress:

Idea: Show that we can embed any list of variants into a big choice.
Maybe its smarter to do this for ADDs and then to conclude by transitivity of translations that CCC Dimension is also complete.

```agda
  module Encode where
    open import Framework.Relation.Function using (_⇔_; to; from)
    open import Data.List.Properties using (map-∘; map-id; map-cong)
    open Eq.≡-Reasoning

    encode : ∀ {i} {A} → Rose i A → CCC Dimension ∞ A
    encode (a V.-< cs >-) = a -< map encode cs >-

    confs : ⊤ ⇔ Config (CCCL Dimension)
    confs = record
      { to = λ where tt _ → 0
      ; from = λ _ → tt
      }

    ccc-encode-idemp : ∀ {A} (v : Rose ∞ A) → (c : Configuration Dimension) → ⟦ encode v ⟧ c ≡ v
    ccc-encode-idemp {A} v@(a V.-< cs >-) c =
      begin
        ⟦ encode v ⟧ c
      ≡⟨⟩
        a V.-< map (λ x → ⟦ x ⟧ c) (map encode cs) >-
      ≡⟨ Eq.cong (a V.-<_>-) (map-∘ cs) ⟨
        a V.-< map (λ x → ⟦ encode x ⟧ c) cs >-
      ≡⟨ Eq.cong (a V.-<_>-) (go cs) ⟩
        v
      ∎
      where
      go : (cs' : List (Rose ∞ A)) → map (λ c' → ⟦ encode c' ⟧ c) cs' ≡ cs'
      go [] = refl
      go (c' ∷ cs') = Eq.cong₂ _∷_ (ccc-encode-idemp c' c) (go cs')

    preserves : ∀ {A} → (v : Rose ∞ A)
      → Semantics (Variant-is-VL (Rose ∞)) v ≅[ to confs ][ from confs ] ⟦ encode v ⟧
    preserves {A} v = irrelevant-index-≅ v
      (λ { tt → refl })
      (ccc-encode-idemp v)
      (to confs)
      (from confs)

    encoder : VariantEncoder (Rose ∞) (CCCL Dimension)
    encoder = record
      { compile = encode
      ; config-compiler = λ _ → confs
      ; preserves = preserves
      }
```


## Utility

```agda
  -- get all dimensions used in a CCC Dimension expression
  open Data.List using (concatMap)

  dims : ∀ {i : Size} {A : 𝔸} → CCC Dimension i A → List Dimension
  dims (_ -< es >-) = concatMap dims es
  dims (D ⟨ es ⟩) = D ∷ concatMap dims (toList es)
```

## Show

```agda
  open import Show.Lines hiding (map)
  open import Data.String as String using (String; _++_)

  show : ∀ {i} → (Dimension → String) → CCC Dimension i (String , String._≟_) → String
  show _ (a -< [] >-) = a
  show show-D (a -< es@(_ ∷ _) >- ) = a ++ "-<" ++ (foldl _++_ "" (map (show show-D) es)) ++ ">-"
  show show-D (D ⟨ es ⟩) = show-D D ++ "⟨" ++ (String.intersperse ", " (toList (map⁺ (show show-D) es))) ++ "⟩"

  pretty : ∀ {i : Size} → (Dimension → String) → CCC Dimension i (String , String._≟_) → Lines
  pretty show-D (a -< [] >-) = > a
  pretty show-D (a -< es@(_ ∷ _) >-) = do
    > a ++ "-<"
    indent 2 do
      intersperseCommas (map (pretty show-D) es)
    > ">-"
  pretty show-D (D ⟨ cs ⟩) = do
    > show-D D ++ "⟨"
    indent 2 do
      intersperseCommas (map (pretty show-D) (toList cs))
    > "⟩"
```
