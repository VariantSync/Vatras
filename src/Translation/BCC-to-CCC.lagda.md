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

open import Lang.Annotation.Dimension using (Dimension)
open import Lang.CC using (CC; Artifact; _⟨_⟩; Tag; Configuration; ⟦_⟧; choice-elimination)
open import Lang.BCC using (CC₂; Artifact₂; _⟨_,_⟩₂; Tag₂; Configuration₂; ⟦_⟧₂)

open import SemanticDomains using (Variant; Artifactᵥ)
open import Translation.Translation
  -- Names
  using (VarLang; ConfLang; Domain; Semantics)
  -- Relations between variability languages
  using (_,_is-as-expressive-as_,_)
  -- Translations
  using (Translation; conf; fnoc)
  -- Translation properties
  using (_⊆-via_; _⊇-via_; _is-variant-preserving; _is-semantics-preserving; translation-proves-variant-preservation)

open import Extensionality
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
toCC : ∀ {i : Size} {A : Set} → CC₂ i A → CC i A
toCC (Artifact₂ a es) = Artifact a (mapl toCC es)
toCC (D ⟨ l , r ⟩₂) = D ⟨ (toCC l) ∷ (toCC r) ∷ [] ⟩

-- Conversion of configurations.
{-
When converting configurations for toCC, we have decide on a possible mapping between booleans and natural numbers.
We chose a mapping that preserves semantics:
true means going left in a binary expression, as does 0 in an n-ary choice calculus expression.
Analoguous for false.
-}
asTag : Tag₂ → Tag
asTag true  = 0
asTag false = 1

asTag₂ : Tag → Tag₂
asTag₂ zero    = true
asTag₂ (suc n) = false

{- |
Convert binary configuration to n-ary configuration.
Only valid for our translation from CC₂ to CC.
-}
toNaryConfig : Configuration₂ → Configuration
toNaryConfig c₂ = asTag ∘ c₂

{- |
Convert n-ary configuration to binary.
Only valid for our translation from CC₂ to CC.
-}
toBinaryConfig : Configuration → Configuration₂
toBinaryConfig c = asTag₂ ∘ c

CC₂→CC : Translation CC₂ CC Configuration₂ Configuration
CC₂→CC = record
  { sem₁ = ⟦_⟧₂
  ; sem₂ = ⟦_⟧
  ; size = λ i → i
  ; lang = toCC
  ; conf = toNaryConfig
  ; fnoc = toBinaryConfig
  }
```

## Properties

```agda
CC₂→CC-left : ∀ {i : Size} {A : Domain}
  → (cc₂-expr : CC₂ i A)
    ---------------------
  → cc₂-expr ⊆-via CC₂→CC

CC₂→CC-right : ∀ {i : Size} {A : Domain}
  → (cc₂-expr : CC₂ i A)
    ---------------------
  → cc₂-expr ⊇-via CC₂→CC

conf-remains-same :
    (c₂ : Configuration₂)
  → (d : Dimension)
    ----------------------------
  → asTag₂ (asTag (c₂ d)) ≡ c₂ d
conf-remains-same c₂ d with c₂ d
... | true  = refl
... | false = refl

CC₂→CC-is-variant-preserving : CC₂→CC is-variant-preserving
CC₂→CC-is-variant-preserving e = CC₂→CC-left e , CC₂→CC-right e

CC₂→CC-is-semantics-preserving : CC₂→CC is-semantics-preserving
CC₂→CC-is-semantics-preserving = CC₂→CC-is-variant-preserving , extensionality ∘ conf-remains-same

CC-is-as-expressive-as-CC₂ : CC , ⟦_⟧ is-as-expressive-as CC₂ , ⟦_⟧₂
CC-is-as-expressive-as-CC₂ = translation-proves-variant-preservation CC₂→CC CC₂→CC-is-variant-preserving
```

## Proofs

### Proof of the left side

```agda
-- helper function for choices
CC₂→CC-left-choice-case-analyses : ∀ {i : Size} {A : Set} {D : Dimension} {l : CC₂ i A} {r : CC₂ i A}
  → ∀ (c₂ : Configuration₂)
    ---------------------------------------------------------------------------------------
  →   ⟦ (if c₂ D then l else r) ⟧₂ c₂
    ≡ ⟦ (choice-elimination (toNaryConfig c₂ D) (toCC l ∷ toCC r ∷ [])) ⟧ (toNaryConfig c₂)
CC₂→CC-left-choice-case-analyses {i} {A} {D} {l} {r} c₂ with c₂ D
... | true  = ⟦ if true then l else r ⟧₂ c₂                                       ≡⟨⟩
              ⟦ l ⟧₂ c₂                                                           ≡⟨ CC₂→CC-left l c₂ ⟩
              ⟦ toCC l ⟧ (toNaryConfig c₂)                                        ≡⟨⟩
              ⟦ (choice-elimination 0 (toCC l ∷ toCC r ∷ [])) ⟧ (toNaryConfig c₂) ∎
    -- This proof is analoguous to the proof for the "true" case.
    -- Thus, we simplify the step-by-step-proof to the only reasoning necessary.
... | false = CC₂→CC-left r c₂

open import Data.List.Properties renaming (map-∘ to mapl-∘)

-- Curiously, the proof is easier for choices than for artifacts.
-- For some reason it was really hard to just prove the application of the induction hypothesis over all subtrees for Artifacts.
-- The use of flip and map made it hard.

-- If we have just artifact leaves, there is nothing left to do.
CC₂→CC-left (Artifact₂ a []) c₂ = refl
-- The semantics "just" recurses on Artifacts.
CC₂→CC-left (Artifact₂ a es@(_ ∷ _)) c₂ =
  ⟦ Artifact₂ a es ⟧₂ c₂                                        ≡⟨⟩
  Artifactᵥ a (mapl (λ x → ⟦ x ⟧₂ c₂) es)                        ≡⟨ Eq.cong (λ m → Artifactᵥ a (m es)) -- apply the induction hypothesis below the Artifactᵥ constructor
                                                                   ( mapl-cong-≗-≡ -- and below the mapl
                                                                     (λ {v → CC₂→CC-left v c₂})
                                                                   )
                                                                  ⟩
  Artifactᵥ a (mapl (flip (⟦_⟧ ∘ toCC) (toNaryConfig c₂)) es)    ≡⟨ Eq.cong (λ m → Artifactᵥ a m) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ (toNaryConfig c₂)) (mapl toCC es)) ≡⟨⟩
  (⟦ toCC (Artifact₂ a es) ⟧ (toNaryConfig c₂))                  ∎
-- The proof for choices could be greatly simplified because when doing a case analyses on (c₂ D), only the induction hypthesis
-- is necessary for reasoning. We leave the long proof version though because it better explains the proof.
CC₂→CC-left (D ⟨ l , r ⟩₂) c₂ =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ c₂                                                                   ≡⟨⟩
  ⟦ if c₂ D then l else r ⟧₂ c₂                                                         ≡⟨ CC₂→CC-left-choice-case-analyses c₂ ⟩
  ⟦ choice-elimination ((toNaryConfig c₂) D) (toCC l ∷ toCC r ∷ []) ⟧ (toNaryConfig c₂) ≡⟨⟩
  ⟦ D ⟨ toCC l ∷ toCC r ∷ [] ⟩ ⟧ (toNaryConfig c₂)                                       ≡⟨⟩
  ⟦ toCC (D ⟨ l , r ⟩₂) ⟧ (toNaryConfig c₂)                                              ∎
```

### Proof of the right side

This proof is very similar to the left side. Maybe we can simplify both proofs if we extract some similarities.
```agda
-- case analyses for choices where we either have to proceed the proof on the left or right side of a binary choice depending on our configuration
CC₂→CC-right-choice-case-analysis : ∀ {i : Size} {A : Set} {D : Dimension} {l r : CC₂ i A}
  → ∀ (c : Configuration)
    -------------------------------------------------------
  →   ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c)
    ≡ ⟦ choice-elimination (c D) (toCC l ∷ toCC r ∷ []) ⟧ c
CC₂→CC-right-choice-case-analysis {i} {A} {D} {l} {r} c with c D
... | zero  = CC₂→CC-right l c
... | suc n = CC₂→CC-right r c

CC₂→CC-right (Artifact₂ a []) c = refl
CC₂→CC-right (Artifact₂ a es@(_ ∷ _)) c =
  ⟦ Artifact₂ a es ⟧₂ (toBinaryConfig c)               ≡⟨⟩
  Artifactᵥ a (mapl (flip ⟦_⟧₂ (toBinaryConfig c)) es) ≡⟨ Eq.cong (λ {m → Artifactᵥ a (m es)}) (mapl-cong-≗-≡ (λ {v → CC₂→CC-right v c})) ⟩
  Artifactᵥ a (mapl ((flip ⟦_⟧ c) ∘ toCC) es)           ≡⟨ Eq.cong (λ {x → Artifactᵥ a x}) (mapl-∘ es) ⟩
  Artifactᵥ a (mapl (flip ⟦_⟧ c) (mapl toCC es))       ≡⟨⟩
  ⟦ toCC (Artifact₂ a es) ⟧ c                          ∎
CC₂→CC-right (D ⟨ l , r ⟩₂) c =
  ⟦ D ⟨ l , r ⟩₂ ⟧₂ (toBinaryConfig c)                   ≡⟨⟩
  ⟦ if asTag₂ (c D) then l else r ⟧₂ (toBinaryConfig c) ≡⟨ CC₂→CC-right-choice-case-analysis c ⟩
  ⟦ choice-elimination (c D) (toCC l ∷ toCC r ∷ []) ⟧ c ≡⟨⟩
  ⟦ D ⟨ toCC l ∷ toCC r ∷ [] ⟩ ⟧ c                       ≡⟨⟩
  ⟦ toCC (D ⟨ l , r ⟩₂) ⟧ c                              ∎
```
