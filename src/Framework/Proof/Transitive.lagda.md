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
completeness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage V}
  → Complete L₂
  → L₁ ≽ L₂
    -----------------------------------
  → Complete L₁
completeness-by-expressiveness encode-in-L₂ L₂-to-L₁ {A} vs with encode-in-L₂ vs
... | e₂ , m≅e₂ with L₂-to-L₁ e₂
...   | e₁ , e₂≅e₁ = e₁ , ≅-trans m≅e₂ e₂≅e₁

incompleteness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage V}
  → Incomplete L₁
  → L₁ ≽ L₂
    -----------------------------------
  → Incomplete L₂
incompleteness-by-expressiveness L₁-incomp L₁≽L₂ L₂-comp = L₁-incomp (completeness-by-expressiveness L₂-comp L₁≽L₂)
```

If a language `L₁` is sound and at least as expressive as another language `L₂`, then also `L₂` is sound.
The intuition is that `L₁` can express everything `L₂` and everything expressed by `L₁` is valid.
So also everything expressed in `L₂` must be valid.
```agda
soundness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage V}
  → Sound L₁
  → L₁ ≽ L₂
    --------
  → Sound L₂
soundness-by-expressiveness L₁-sound L₂-to-L₁ {A} e₂ with L₂-to-L₁ e₂
... | e₁ , e₂≅e₁ with L₁-sound e₁
...   | n , m , m≅e₁ = n , m , ≅-trans m≅e₁ (≅-sym e₂≅e₁)

unsoundness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage V}
  → Unsound L₂
  → L₁ ≽ L₂
    -----------------------------------
  → Unsound L₁
unsoundness-by-expressiveness L₂-unsound L₁≽L₂ L₂-sound = L₂-unsound (soundness-by-expressiveness L₂-sound L₁≽L₂)
```

Conversely, we can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression e of our target language L, we have to show that there exists an expression e₊ in our complete language L₊ that is variant-equivalent to e.
Given the semantics S of the complete language L of e, we compute the set of all variants described by e, as a list (THIS IS STILL LEFT TODO).
Since L₊ is complete, we can encode this list of variants in L₊, giving us an expression in e₊ in L₊ and a proof that this expression exactly describes the variants of e₋.
Now we conclude from this proof that e₊ is variant-equivalent to e₋ (TODO).
```agda
expressiveness-by-completeness-and-soundness : ∀ {Lᶜ Lˢ : VariabilityLanguage V}
  → Complete Lᶜ
  → Sound Lˢ
    ----------------------------------
  → Lᶜ ≽ Lˢ
expressiveness-by-completeness-and-soundness comp sound {A} eˢ with sound eˢ
... | p , m , m≅⟦eˢ⟧ with comp m
...   | eᶜ , m≅⟦eᶜ⟧ = eᶜ , ≅-trans (≅-sym m≅⟦eˢ⟧) m≅⟦eᶜ⟧
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

Combined with `expressiveness-by-completeness` we can even further conclude that L₊ is more expressive than L₋:
```agda
more-expressive : ∀ {L₊ L₋ : VariabilityLanguage V}
  → Complete L₊
  → Sound L₋
  → Incomplete L₋
    ------------------------------
  → L₊ ≻ L₋
more-expressive {L₊} {L₋} L₊-comp L₋-sound L₋-incomp =
    expressiveness-by-completeness-and-soundness L₊-comp L₋-sound
  , less-expressive-from-completeness L₊-comp L₋-incomp
```

```agda
complete-is-most-expressive : ∀ {L₁ : VariabilityLanguage V}
  → Complete L₁
    ----------------
  → ∄[ L₂ ] (Sound L₂ × L₂ ≻ L₁)
complete-is-most-expressive L₁-comp (L₂ , L₂-sound , L₂≽L₁ , L₁⋡L₂) =
  L₁⋡L₂ (expressiveness-by-completeness-and-soundness L₁-comp L₂-sound)
```
