# Theorems to Prove Completeness

```agda
{-# OPTIONS --sized-types #-}

module Lang.Properties.Conclude.Completeness where

open import Data.Product using (_,_)

open import Function using (_∘_)
open import Size using (∞)

open import Definitions
open import Relations.Semantic
open import Lang.Properties.Completeness
open import Lang.Properties.Soundness

import Data.IndexedSet
private module ISet A = Data.IndexedSet (VariantSetoid ∞ A)
```

## Conclusions

If a language `L₁` is complete, and another language `L₂` is as expressive as `L₁`, then also `L₂` is complete.
The intuition is that `L₂` can express everything `L₁` can express which in turn is "everything" by completeness.
Thus also `L₂` is complete.

**Proof Sketch:**
Let V be an arbitrary set of variants.
Since L₁ is complete, there exists an expression e₁ ∈ L₁ that describes V.
By assumption, L₂ is as expressive as L₁.
Thus, there exists an expression e₂ ∈ L₂ that also describes V.
Since V was picked arbitrarily, L₂ can encode any set of variants.
Thus, L₂ is complete.
```agda
completeness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage}
  → Complete L₁
  → L₂ is-at-least-as-expressive-as L₁
    -----------------------------------
  → Complete L₂
completeness-by-expressiveness encode-in-L₁ L₁-to-L₂ vs with encode-in-L₁ vs
... | e₁ , vs≅e₁ with L₁-to-L₂ e₁
...   | e₂ , e₁≅e₂ = e₂ , ≅-trans vs≅e₁ e₁≅e₂
  where open ISet _ using (≅-trans)
```

Conversely, we can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression e of our target language L, we have to show that there exists an expression e₊ in our complete language L₊ that is variant-equivalent to e.
Given the semantics S of the complete language L of e, we compute the set of all variants described by e, as a list (THIS IS STILL LEFT TODO).
Since L₊ is complete, we can encode this list of variants in L₊, giving us an expression in e₊ in L₊ and a proof that this expression exactly describes the variants of e₋.
Now we conclude from this proof that e₊ is variant-equivalent to e₋ (TODO).
```agda
expressiveness-by-completeness-and-soundness : ∀ {Lᶜ Lˢ : VariabilityLanguage}
  → Complete Lᶜ
  → Sound Lˢ
    ----------------------------------
  → Lᶜ is-at-least-as-expressive-as Lˢ
expressiveness-by-completeness-and-soundness {L₊} L₊-comp L-sound {A = A} eˢ with L-sound eˢ
... | n , vsetₑ , vsetₑ≅⟦eˢ⟧ with L₊-comp vsetₑ
...   | eᶜ , vsetₑ≅⟦eᶜ⟧ᶜ = eᶜ , ≅-trans (≅-sym vsetₑ≅⟦eˢ⟧) vsetₑ≅⟦eᶜ⟧ᶜ
  where open ISet A using (≅-sym; ≅-trans)
```

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.

**Proof sketch:**
Assuming `L₋` is as expressive as `L₊`, and knowing that `L₊` is complete, we can conclude that also `L₋` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that L₋ is incomplete.
This yields a contradiction.
```agda
less-expressive-from-completeness : ∀ {L₊ L₋ : VariabilityLanguage}
  →   Complete L₊
  → Incomplete L₋
    ------------------------------
  → L₋ is-less-expressive-than L₊
less-expressive-from-completeness L₊-comp L₋-incomp L₋-as-expressive-as-L₊ =
    L₋-incomp (completeness-by-expressiveness L₊-comp L₋-as-expressive-as-L₊)
```

Combined with `expressiveness-by-completeness` we can even further conclude that L₊ is more expressive than L₋:
```agda
more-expressive-from-completeness : ∀ {L₊ L₋ : VariabilityLanguage}
  → Complete L₊
  → Sound L₋
  → Incomplete L₋
    ------------------------------
  → L₊ is-more-expressive-than L₋
more-expressive-from-completeness {L₊} {L₋} L₊-comp L₋-sound L₋-incomp =
    expressiveness-by-completeness-and-soundness L₊-comp L₋-sound
  , less-expressive-from-completeness L₊-comp L₋-incomp
```
