# Relating Binary Choice Calculus to Core Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.BCC-to-CCC where
```

## Imports

```agda
-- stdlib
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.Properties
  renaming (map-∘ to mapl-∘)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat
  using (ℕ; zero; suc; NonZero)
open import Data.Product
  using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Function
  using (_∘_; flip)
open import Size
  using (Size)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- own modules

open import Lang.Annotation.Name using (Dimension)
open import Lang.CCC
  using (CCC; choice-elimination)
  renaming (Artifact to Artifactₙ;
            _⟨_⟩ to _⟨_⟩ₙ;
            Tag to Tagₙ;
            Configuration to Configurationₙ;
            ⟦_⟧ to ⟦_⟧ₙ)
open import Lang.BCC
  using (BCC)
  renaming (Artifact to Artifact₂;
            _⟨_,_⟩ to _⟨_,_⟩₂;
            Tag to Tag₂;
            Configuration to Configuration₂;
            ⟦_⟧ to ⟦_⟧₂)

open import SemanticDomain using (Variant; Artifactᵥ)
open import Translation.Translation
  -- Names
  using (VarLang; ConfLang; Domain; Semantics; Translation; getSize)
  -- Relations between variability languages
  using (_,_is-as-expressive-as_,_)
  -- Translation properties
  using (_⊆-via_; _⊇-via_; _is-variant-preserving; _is-semantics-preserving; translation-proves-variant-preservation)

open import Axioms.Extensionality
  using (extensionality; _embeds-via_)
  renaming (map-cong-≡ to mapl-cong-≡; map-cong-≗-≡ to mapl-cong-≗-≡)
```

## Translation

Our goal is to convert a choice calculus expression of which we know at the type level that it is in binary normal form, back to n-ary choice calculus. It will still be an expression in binary normal form but we will lose that guarantee at the type level.


```agda
{- |
Converts a binary choice calculus expression to a core choice calculus expression.
The resulting expression is syntactically equivalent and thus still in binary normal form.
We only drop the knowledge of being in binary normal form at the type level.
-}
toCCC : ∀ {i : Size} {A : Set} → BCC i A → CCC i A
toCCC (Artifact₂ a es) = Artifactₙ a (mapl toCCC es)
toCCC (D ⟨ l , r ⟩₂) = D ⟨ (toCCC l) ∷ (toCCC r) ∷ [] ⟩ₙ

open import Util.Existence using (∃-Size; _,_)

-- Conversion of configurations.
{-
When converting configurations for toCC, we have decide on a possible mapping between booleans and natural numbers.
We chose a mapping that preserves semantics:
true means going left in a binary expression, as does 0 in an n-ary choice calculus expression.
Analoguous for false.
-}
asTagₙ : Tag₂ → Tagₙ
asTagₙ true  = 0
asTagₙ false = 1

asTag₂ : Tagₙ → Tag₂
asTag₂ zero    = true
asTag₂ (suc n) = false

{- |
Convert binary configuration to n-ary configuration.
Only valid for our translation from BCC to CCC.
-}
toNaryConfig : Configuration₂ → Configurationₙ
toNaryConfig c₂ = asTagₙ ∘ c₂

{- |
Convert n-ary configuration to binary.
Only valid for our translation from BCC to CCC.
-}
toBinaryConfig : Configurationₙ → Configuration₂
toBinaryConfig c = asTag₂ ∘ c

translate : ∀ {i : Size} {D : Domain} → BCC i D → Translation.Translation.TranslationResult D CCC Configuration₂ Configurationₙ
translate {i} {D} e = record
  { size = i
  ; expr = toCCC e
  ; conf = toNaryConfig
  ; fnoc = toBinaryConfig
  }

BCC→CCC : Translation BCC CCC Configuration₂ Configurationₙ
BCC→CCC = record
  { sem₁ = ⟦_⟧₂
  ; sem₂ = ⟦_⟧ₙ
  ; translate = translate
  }
```

## Properties

```agda
BCC→CCC-left : ∀ {i : Size} {A : Domain}
  → (e : BCC i A)
    ---------------------
  → e ⊆-via BCC→CCC

BCC→CCC-right : ∀ {i : Size} {A : Domain}
  → (e : BCC i A)
    ---------------------
  → e ⊇-via BCC→CCC

conf-remains-same :
    (c₂ : Configuration₂)
  → (d : Dimension)
    ----------------------------
  → asTag₂ (asTagₙ (c₂ d)) ≡ c₂ d
conf-remains-same c₂ d with c₂ d
... | true  = refl
... | false = refl

BCC→CCC-is-variant-preserving : BCC→CCC is-variant-preserving
BCC→CCC-is-variant-preserving e = BCC→CCC-left e , BCC→CCC-right e

BCC→CCC-is-semantics-preserving : BCC→CCC is-semantics-preserving
BCC→CCC-is-semantics-preserving = BCC→CCC-is-variant-preserving , λ _ → extensionality ∘ conf-remains-same

CCC-is-as-expressive-as-BCC : CCC , ⟦_⟧ₙ is-as-expressive-as BCC , ⟦_⟧₂
CCC-is-as-expressive-as-BCC = translation-proves-variant-preservation BCC→CCC BCC→CCC-is-variant-preserving
```

## Proofs

### Proof of the left side

```agda
-- helper function for choices
BCC→CCC-left-choice-case-analyses : ∀ {i : Size} {A : Set} {D : Dimension} {l : BCC i A} {r : BCC i A}
  → ∀ (c₂ : Configuration₂)
    ------------------------------------------------------------------------------------------
  →   ⟦ (if c₂ D then l else r) ⟧₂ c₂
    ≡ ⟦ (choice-elimination (toNaryConfig c₂ D) (toCCC l ∷ toCCC r ∷ [])) ⟧ₙ (toNaryConfig c₂)
BCC→CCC-left-choice-case-analyses {i} {A} {D} {l} {r} c₂ with c₂ D
... | true  = ⟦ if true then l else r ⟧₂ c₂                                         ≡⟨⟩
              ⟦ l ⟧₂ c₂                                                             ≡⟨ BCC→CCC-left l c₂ ⟩
              ⟦ toCCC l ⟧ₙ (toNaryConfig c₂)                                         ≡⟨⟩
              ⟦ (choice-elimination 0 (toCCC l ∷ toCCC r ∷ [])) ⟧ₙ (toNaryConfig c₂) ∎
    -- This proof is analoguous to the proof for the "true" case.
    -- Thus, we simplify the step-by-step-proof to the only reasoning necessary.
... | false = BCC→CCC-left r c₂

-- Curiously, the proof is easier for choices than for artifacts.
-- For some reason it was really hard to just prove the application of the induction hypothesis over all subtrees for Artifacts.
-- The use of flip and map made it hard.

-- If we have just artifact leaves, there is nothing left to do.
BCC→CCC-left (Artifact₂ a []) c₂ = refl
-- The semantics "just" recurses on Artifacts.
BCC→CCC-left (Artifact₂ a es@(_ ∷ _)) c₂ =
  ⟦ Artifact₂ a es ⟧₂ c₂                                         ≡⟨⟩
  Artifactᵥ a (mapl (λ x → ⟦ x ⟧₂ c₂) es)                         ≡⟨ Eq.cong (λ m → Artifactᵥ a (m es)) -- apply the induction hypothesis below the Artifactᵥ constructor
                                                                    ( mapl-cong-≗-≡ -- and below the mapl
                                                                      (λ {v → BCC→CCC-left v c₂})
                                                                    )
                                                                  ⟩
  Artifactᵥ a (mapl (flip (⟦_⟧ₙ ∘ toCCC) (toNaryConfig c₂)) es)    ≡⟨ Eq.cong (λ m → Artifactᵥ a m) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ₙ (toNaryConfig c₂)) (mapl toCCC es)) ≡⟨⟩
  (⟦ toCCC (Artifact₂ a es) ⟧ₙ (toNaryConfig c₂))                  ∎
-- The proof for choices could be greatly simplified because when doing a case analyses on (c₂ D), only the induction hypthesis
-- is necessary for reasoning. We leave the long proof version though because it better explains the proof.
BCC→CCC-left (D ⟨ l , r ⟩₂) c₂ =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ c₂                                                                     ≡⟨⟩
  ⟦ if c₂ D then l else r ⟧₂ c₂                                                            ≡⟨ BCC→CCC-left-choice-case-analyses c₂ ⟩
  ⟦ choice-elimination ((toNaryConfig c₂) D) (toCCC l ∷ toCCC r ∷ []) ⟧ₙ (toNaryConfig c₂) ≡⟨⟩
  ⟦ D ⟨ toCCC l ∷ toCCC r ∷ [] ⟩ₙ ⟧ₙ (toNaryConfig c₂)                                      ≡⟨⟩
  ⟦ toCCC (D ⟨ l , r ⟩₂) ⟧ₙ (toNaryConfig c₂)                                               ∎
```

### Proof of the right side

This proof is very similar to the left side. Maybe we can simplify both proofs if we extract some similarities.
```agda
-- case analyses for choices where we either have to proceed the proof on the left or right side of a binary choice depending on our configuration
BCC→CCC-right-choice-case-analysis : ∀ {i : Size} {A : Set} {D : Dimension} {l r : BCC i A}
  → ∀ (c : Configurationₙ)
    -------------------------------------------------------
  →   ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)
    ≡ ⟦ choice-elimination (c D) (toCCC l ∷ toCCC r ∷ []) ⟧ₙ c
BCC→CCC-right-choice-case-analysis {i} {A} {D} {l} {r} c with c D
... | zero  = BCC→CCC-right l c
... | suc n = BCC→CCC-right r c

BCC→CCC-right (Artifact₂ a []) c = refl
BCC→CCC-right (Artifact₂ a es@(_ ∷ _)) c =
  ⟦ Artifact₂ a es ⟧₂ (toBinaryConfig c)               ≡⟨⟩
  Artifactᵥ a (mapl (flip ⟦_⟧₂ (toBinaryConfig c)) es) ≡⟨ Eq.cong (λ {m → Artifactᵥ a (m es)}) (mapl-cong-≗-≡ (λ {v → BCC→CCC-right v c})) ⟩
  Artifactᵥ a (mapl ((flip ⟦_⟧ₙ c) ∘ toCCC) es)         ≡⟨ Eq.cong (λ {x → Artifactᵥ a x}) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ₙ c) (mapl toCCC es))      ≡⟨⟩
  ⟦ toCCC (Artifact₂ a es) ⟧ₙ c                         ∎
BCC→CCC-right (D ⟨ l , r ⟩₂) c =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ (toBinaryConfig c)                     ≡⟨⟩
  ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)    ≡⟨ BCC→CCC-right-choice-case-analysis c ⟩
  ⟦ choice-elimination (c D) (toCCC l ∷ toCCC r ∷ []) ⟧ₙ c ≡⟨⟩
  ⟦ D ⟨ toCCC l ∷ toCCC r ∷ [] ⟩ₙ ⟧ₙ c                      ≡⟨⟩
  ⟦ toCCC (D ⟨ l , r ⟩₂) ⟧ₙ c                               ∎
```
