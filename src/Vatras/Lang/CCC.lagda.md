# Core Choice Calculus

```agda
open import Vatras.Framework.Definitions
module Vatras.Lang.CCC where
```

## Imports
```agda
open import Data.List using (List; []; _∷_; foldl; map)
open import Data.List.NonEmpty using (List⁺; _∷_; toList) renaming (map to map⁺)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open import Data.Nat using (ℕ)

open import Function using (id; _∘_; _$_)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose; VariantEncoder; Variant-is-VL)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Util.List using (find-or-last)

open import Vatras.Data.EqIndexedSet as ISet
```

## Syntax

A core choice calculus expression is either an artifact `a -< es >-` (just as in [rose trees](../Framework/Variants.agda))
or a choice `D ⟨ as ⟩` with an arbitrarily many but at least one alternative `as`.
```agda
data CCC (Dimension : 𝔽) : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (CCC Dimension i A) → CCC Dimension (↑ i) A
   _⟨_⟩ : ∀ {i A} → Dimension → List⁺ (CCC Dimension i A) → CCC Dimension (↑ i) A
```

## Semantics

The core choice calculus has denotational semantics.
Semantics for choice calculus have been defined in different ways.
- As a set of pairs `Configuration × Variant`
- As a configuration function `Configuration → Variant` that generates variants from configurations.

The second definition separates the concerns of (1) generating a variant, and (2) enumerating all possible variants.
Enumeration of variants is still possible by generating all possible configurations first.
Thus, and for much simpler proofs, we choose the functional semantics.

First, we define configurations as functions that evaluate dimensions by choosing an alternative.
While choices have a fixed and finite amount of alternatives, we allow the configuration to produce
any natural number for simplicity here (in case of an overlow, we will just pick the last alternative).
This formulation is a simplification of the original choice calculus in which alternatives are identified by _tags_
and then configurations choose tags.
The simplification here is analogous to how de Bruijn indices simplify lambda calculus.
```agda
Configuration : (Dimension : 𝔽) → ℂ
Configuration Dimension = Dimension → ℕ
```

We can now define the semantics.
In case a configuration picks an undefined tag for a dimension (i.e., a number larger than the amount of alternatives within a choice), we chose the last alternative as a fallback.
This allows us to avoid complex error handling or typing rules to ensure that a  configuration only produces valid tags.
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

Some interesting properties:

```agda
  module Properties where
    open import Vatras.Framework.Relation.Expression (Rose ∞)

    module _ {A : 𝔸} where
      {-|
      Unary choices are mandatory.
      -}
      D⟨e⟩≣e : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          -----------------------------
        → CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≣₁ e
      D⟨e⟩≣e _ = refl

      -- other way to prove the above

      D⟨e⟩⊆e : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          ---------------------------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≤ e
      D⟨e⟩⊆e c = c , refl

      e⊆D⟨e⟩ : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          ---------------------------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ e ≤ D ⟨ e ∷ [] ⟩
      e⊆D⟨e⟩ c = c , refl

      D⟨e⟩≣e' : ∀ {e : CCC Dimension ∞ A} {D : Dimension}
          --------------------------------------------------
        → CCCL Dimension , CCCL Dimension ⊢ D ⟨ e ∷ [] ⟩ ≣ e
      D⟨e⟩≣e' {e} {D} = D⟨e⟩⊆e {e} {D} , e⊆D⟨e⟩ {e} {D}
```

## Encoding Variants

Core choice calculus can express singleton systems as well (i.e., domains in which there is only exactly one variant).
Such behavior is implemented in terms of [variant encoders](../Framework/Variants.agda).
We can encode a variant in core choice calculus by using only the artifact constructor and no choices.
```agda
  module Encode where
    open import Vatras.Framework.Relation.Function using (_⇔_; to; from)
    open import Data.List.Properties using (map-∘; map-id; map-cong)
    open Eq.≡-Reasoning

    {-|
    Encode a rose tree in a core choice calculus expression.
    -}
    encode : ∀ {i} {A} → Rose i A → CCC Dimension ∞ A
    encode (a V.-< cs >-) = a -< map encode cs >-

    {-|
    Translating configurations is trivial because their values never matter.
    We can do anything here.
    -}
    confs : ⊤ ⇔ Config (CCCL Dimension)
    confs = record
      { to = λ where tt _ → 0
      ; from = λ _ → tt
      }

    {-|
    Correctness proof of the encoding: We always get our encoded variant back.
    -}
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

    {-|
    Using idempotency, we can prove the formal correctness criterion for variability language compilers.
    -}
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

Recursively, collect all dimensions used in a CCC expression:
```agda
  open Data.List using (concatMap)

  dims : ∀ {i : Size} {A : 𝔸} → CCC Dimension i A → List Dimension
  dims (_ -< es >-) = concatMap dims es
  dims (D ⟨ es ⟩) = D ∷ concatMap dims (toList es)
```

## Show

```agda
  open import Vatras.Show.Lines hiding (map)
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
