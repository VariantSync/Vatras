# Theorems to Prove Completeness

```agda
open import Framework.Definitions using (𝕍)
module Framework.Proof.Transitive (V : 𝕍) where

open import Data.Product using (_,_; _×_; ∄-syntax)
open import Framework.VariabilityLanguage using (VariabilityLanguage)
open import Framework.Properties.Completeness V
open import Framework.Properties.Soundness V
open import Framework.Relation.Expressiveness V
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
completeness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Complete M
  → L ≽ M
    -----------------------------------
  → Complete L
completeness-by-expressiveness encode-in-M M-to-L vs with encode-in-M vs
... | m , vs≅m with M-to-L m
...   | l , m≅l = l , ≅-trans vs≅m m≅l

incompleteness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
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
soundness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Sound L
  → L ≽ M
    --------
  → Sound M
soundness-by-expressiveness L-sound M-to-L m with M-to-L m
... | l , m≅l with L-sound l
...   | n , v , v≅l = n , v , ≅-trans v≅l (≅-sym m≅l)

unsoundness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
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
expressiveness-by-completeness-and-soundness : ∀ {Lᶜ Lˢ : VariabilityLanguage V}
  → Complete Lᶜ
  → Sound Lˢ
    ----------------------------------
  → Lᶜ ≽ Lˢ
expressiveness-by-completeness-and-soundness comp sound eˢ with sound eˢ
... | p , v , v≅⟦eˢ⟧ with comp v
...   | eᶜ , v≅⟦eᶜ⟧ = eᶜ , ≅-trans (≅-sym v≅⟦eˢ⟧) v≅⟦eᶜ⟧
```

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.

**Proof sketch:**
Assuming `L₋` is as expressive as `L₊`, and knowing that `L₊` is complete, we can conclude that also `L₋` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that L₋ is incomplete.
This yields a contradiction.
```agda
less-expressive-from-completeness : ∀ {L₊ L₋ : VariabilityLanguage V}
  →   Complete L₊
  → Incomplete L₋
    ------------------------------
  → L₋ ⋡ L₊
less-expressive-from-completeness L₊-comp L₋-incomp L₋-as-expressive-as-L₊ =
    L₋-incomp (completeness-by-expressiveness L₊-comp L₋-as-expressive-as-L₊)
```

```agda
less-expressive-from-soundness : ∀ {L₊ L₋ : VariabilityLanguage V}
  →   Sound L₊
  → Unsound L₋
    ------------------------------
  → L₊ ⋡ L₋
less-expressive-from-soundness L₊-sound L₋-unsound L₋≽L₊ =
    L₋-unsound (soundness-by-expressiveness L₊-sound L₋≽L₊)
```

Combined with `expressiveness-by-completeness` we can even further conclude that L₊ is more expressive than L₋:
```agda
more-expressive-by-completeness : ∀ {L₊ L₋ : VariabilityLanguage V}
  → Complete L₊
  → Sound L₋
  → Incomplete L₋
    -------------
  → L₊ ≻ L₋
more-expressive-by-completeness L₊-comp L₋-sound L₋-incomp =
    expressiveness-by-completeness-and-soundness L₊-comp L₋-sound
  , less-expressive-from-completeness L₊-comp L₋-incomp

more-expressive-by-soundness : ∀ {L₊ L₋ : VariabilityLanguage V}
  → Sound L₊
  → Complete L₋
  → Unsound L₋
    -----------
  → L₋ ≻ L₊
more-expressive-by-soundness L₊-sound L₋-comp L₋-unsound =
    expressiveness-by-completeness-and-soundness L₋-comp L₊-sound
  , less-expressive-from-soundness L₊-sound L₋-unsound
```

```agda
complete-is-most-expressive : ∀ {L : VariabilityLanguage V}
  → Complete L
    ----------------
  → ∄[ M ] (Sound M × M ≻ L)
complete-is-most-expressive L-comp (M , M-sound , M≽L , L⋡M) =
  L⋡M (expressiveness-by-completeness-and-soundness L-comp M-sound)
```
