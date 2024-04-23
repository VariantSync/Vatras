# Theorems to Prove Completeness

```agda
module Framework.Proof.Transitive where

open import Data.Product using (_,_; _×_; ∄-syntax)
open import Framework.VariabilityLanguage using (VariabilityLanguage)
open import Framework.Properties.Completeness
open import Framework.Properties.Soundness
open import Framework.Relation.Expressiveness
open import Data.EqIndexedSet
```

## Conclusions

If a language `L` is complete, and another language `M` is as expressive as `L`, then also `M` is complete.
The intuition is that `M` can express everything `L` can express which in turn is "everything" by completeness.
Thus also `M` is complete.

**Proof Sketch:**
Let V be an arbitrary set of variants.
Since L is complete, there exists an expression l ∈ L that describes V.
By assumption, M is as expressive as L.
Thus, there exists an expression m ∈ M that also describes V.
Since V was picked arbitrarily, M can encode any set of variants.
Thus, M is complete.
```agda
completeness-by-expressiveness : ∀ {L M : VariabilityLanguage}
  → Complete M
  → L ≽ M
    -----------------------------------
  → Complete L
completeness-by-expressiveness encode-in-M M-to-L vs with encode-in-M vs
... | m , vs≅m with M-to-L m
...   | l , m≅l = l , ≅-trans vs≅m m≅l

incompleteness-by-expressiveness : ∀ {L M : VariabilityLanguage}
  → Incomplete L
  → L ≽ M
    -----------------------------------
  → Incomplete M
incompleteness-by-expressiveness L-incomp L≽M M-comp = L-incomp (completeness-by-expressiveness M-comp L≽M)
```

If a language `L` is sound and at least as expressive as another language `M`, then also `M` is sound.
The intuition is that `L` can express everything `M` and everything expressed by `L` is valid.
So also everything expressed in `M` must be valid.
```agda
soundness-by-expressiveness : ∀ {L M : VariabilityLanguage}
  → Sound L
  → L ≽ M
    --------
  → Sound M
soundness-by-expressiveness L-sound M-to-L m with M-to-L m
... | l , m≅l with L-sound l
...   | n , v , v≅l = n , v , ≅-trans v≅l (≅-sym m≅l)

unsoundness-by-expressiveness : ∀ {L M : VariabilityLanguage}
  → Unsound M
  → L ≽ M
    -----------------------------------
  → Unsound L
unsoundness-by-expressiveness M-unsound L≽M M-sound = M-unsound (soundness-by-expressiveness M-sound L≽M)
```

Conversely, we can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression eˢ of our target language Lˢ, we have to show that there exists an expression e₊ in our complete language Lᶜ that is variant-equivalent to eˢ.
By soundness of Lˢ we can compute the variant map of eˢ.
By completeness of Lᶜ, we can encode any variant map as an expression eᶜ ∈ Lᶜ.
```agda
expressiveness-by-completeness-and-soundness : ∀ {Lᶜ Lˢ : VariabilityLanguage}
  → Complete Lᶜ
  → Sound Lˢ
    ----------------------------------
  → Lᶜ ≽ Lˢ
expressiveness-by-completeness-and-soundness comp sound eˢ with sound eˢ
... | p , v , v≅⟦eˢ⟧ with comp v
...   | eᶜ , v≅⟦eᶜ⟧ = eᶜ , ≅-trans (≅-sym v≅⟦eˢ⟧) v≅⟦eᶜ⟧
```

If a language `L` is complete and another language `M` is incomplete then `M` less expressive than `L`.

**Proof sketch:**
Assuming `M` is as expressive as `L`, and knowing that `L` is complete, we can conclude that also `M` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that M is incomplete.
This yields a contradiction.
```agda
less-expressive-from-completeness : ∀ {L M : VariabilityLanguage}
  →   Complete L
  → Incomplete M
    ------------------------------
  → M ⋡ L
less-expressive-from-completeness L-comp M-incomp M-as-expressive-as-L =
    M-incomp (completeness-by-expressiveness L-comp M-as-expressive-as-L)
```

```agda
less-expressive-from-soundness : ∀ {L M : VariabilityLanguage}
  →   Sound L
  → Unsound M
    ------------------------------
  → L ⋡ M
less-expressive-from-soundness L-sound M-unsound M≽L =
    M-unsound (soundness-by-expressiveness L-sound M≽L)
```

Combined with `expressiveness-by-completeness` we can even further conclude that L is more expressive than M:
```agda
more-expressive-by-completeness : ∀ {L M : VariabilityLanguage}
  → Complete L
  → Sound M
  → Incomplete M
    -------------
  → L ≻ M
more-expressive-by-completeness L-comp M-sound M-incomp =
    expressiveness-by-completeness-and-soundness L-comp M-sound
  , less-expressive-from-completeness L-comp M-incomp

more-expressive-by-soundness : ∀ {L M : VariabilityLanguage}
  → Sound L
  → Complete M
  → Unsound M
    -----------
  → M ≻ L
more-expressive-by-soundness L-sound M-comp M-unsound =
    expressiveness-by-completeness-and-soundness M-comp L-sound
  , less-expressive-from-soundness L-sound M-unsound
```

```agda
complete-is-most-expressive : ∀ {L : VariabilityLanguage}
  → Complete L
    ----------------
  → ∄[ M ] (Sound M × M ≻ L)
complete-is-most-expressive L-comp (M , M-sound , M≽L , L⋡M) =
  L⋡M (expressiveness-by-completeness-and-soundness L-comp M-sound)

complete-is-most-expressive' : ∀ {L : VariabilityLanguage}
  → Sound L
    ----------------
  → ∄[ M ] (Complete M × L ≻ M)
complete-is-most-expressive' {L} L-sound (M , M-comp , L≻M) = complete-is-most-expressive M-comp (L , L-sound , L≻M)
```
