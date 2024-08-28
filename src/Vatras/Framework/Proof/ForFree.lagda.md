# Proofs for Completeness, Soundness, and Expressiveness for Free

This module contains range of theorems that relate completeness, soundness, and expressiveness
in intersting ways, which also gives rise to reuse proofs for some of these properties
to conclude proofs for the other properties.
This module contains the  **Proofs for Free** from Section 4.4. of our paper but
also a range of further interesting proofs for free (e.g., also relating incompleteness and unsoundness
with expressiveness), which did not fit into the paper.

```agda
open import Vatras.Framework.Definitions using (𝕍)
module Vatras.Framework.Proof.ForFree (V : 𝕍) where

open import Data.Product using (_,_; _×_; ∄-syntax)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage)
open import Vatras.Framework.Properties.Completeness V
open import Vatras.Framework.Properties.Soundness V
open import Vatras.Framework.Relation.Expressiveness V
open import Vatras.Data.EqIndexedSet
```

```agda
{-|
If a language `L` is complete, and another language `M` is as expressive as `L`, then also `M` is complete.
The intuition is that `M` can express everything `L` can express which in turn is "everything" by completeness.
Thus also `M` is complete.

**Proof Sketch:**
Let V be an arbitrary variant map.
Since L is complete, there exists an expression l ∈ L that describes V.
By assumption, M is as expressive as L.
Thus, there exists an expression m ∈ M that also describes V.
Since V was picked arbitrarily, M can encode any variant map.
Thus, M is complete.

Dual theorem to: soundness-by-expressiveness.
-}
completeness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Complete M
  → L ≽ M
    -----------
  → Complete L
completeness-by-expressiveness encode-in-M M-to-L vs with encode-in-M vs
... | m , vs≅m with M-to-L m
...   | l , m≅l = l , ≅-trans vs≅m m≅l

{-|
A language M is incomplete if there exists a language L that is at least as expressive.
The intuition is that M cannot be complete as long as there exists
another language which is more expressive (or equally expressive) that
is already proven incomplete.

Dual theorem to: unsoundness-by-expressiveness.
-}
incompleteness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Incomplete L
  → L ≽ M
    ------------
  → Incomplete M
incompleteness-by-expressiveness L-incomp L≽M M-comp = L-incomp (completeness-by-expressiveness M-comp L≽M)

{-|
If a language `L` is sound and at least as expressive as another language `M`, then also `M` is sound.
The intuition is that `L` can express everything `M` and everything expressed by `L` is valid.
So also everything expressed in `M` must be valid.

Dual theorem to: completeness-by-expressiveness.
-}
soundness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Sound L
  → L ≽ M
    --------
  → Sound M
soundness-by-expressiveness L-sound M-to-L m with M-to-L m
... | l , m≅l with L-sound l
...   | n , v , v≅l = n , v , ≅-trans v≅l (≅-sym m≅l)

{-|
A language L is unsound if it is at least as expressive as another unsound language M.
The intuition is that there are expressions in M that describe something else
than a variant map.
Since L is at least as expressive as M, L can also express these other things.
Hence, L cannot be sound as well.

Dual theorem to: incompleteness-by-expressiveness.
-}
unsoundness-by-expressiveness : ∀ {L M : VariabilityLanguage V}
  → Unsound M
  → L ≽ M
    -----------------------------------
  → Unsound L
unsoundness-by-expressiveness M-unsound L≽M M-sound = M-unsound (soundness-by-expressiveness M-sound L≽M)

{-|
We can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression eˢ of our target language Lˢ, we have to show that there exists an expression e₊ in our complete language Lᶜ that is variant-equivalent to eˢ.
By soundness of Lˢ we can compute the variant map of eˢ.
By completeness of Lᶜ, we can encode any variant map as an expression eᶜ ∈ Lᶜ.
-}
expressiveness-by-completeness-and-soundness : ∀ {Lᶜ Lˢ : VariabilityLanguage V}
  → Complete Lᶜ
  → Sound Lˢ
    ----------------------------------
  → Lᶜ ≽ Lˢ
expressiveness-by-completeness-and-soundness comp sound eˢ with sound eˢ
... | p , v , v≅⟦eˢ⟧ with comp v
...   | eᶜ , v≅⟦eᶜ⟧ = eᶜ , ≅-trans (≅-sym v≅⟦eˢ⟧) v≅⟦eᶜ⟧

{-|
Incomplete languages are less expressive than complete languages.

**Proof sketch:**
Assuming `M` is as expressive as `L`, and knowing that `L` is complete, we can conclude that also `M` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that M is incomplete.
This yields a contradiction.

Dual theorem to: less-expressive-from-soundness.
-}
less-expressive-from-completeness : ∀ {L M : VariabilityLanguage V}
  →   Complete L
  → Incomplete M
    ------------------------------
  → M ⋡ L
less-expressive-from-completeness L-comp M-incomp M-as-expressive-as-L =
    M-incomp (completeness-by-expressiveness L-comp M-as-expressive-as-L)

{-|
Sound languages cannot be at least as expressive as unsound languages.
The intuition is that an unsound language can denote things a sound language cannot.

Dual theorem to: less-expressive-from-completeness.
-}
less-expressive-from-soundness : ∀ {L M : VariabilityLanguage V}
  →   Sound L
  → Unsound M
    ------------------------------
  → L ⋡ M
less-expressive-from-soundness L-sound M-unsound M≽L =
    M-unsound (soundness-by-expressiveness L-sound M≽L)
```

Combined with `expressiveness-by-completeness`/`expressiveness-by-soundness` we can even further conclude that L is more expressive than M or vice versa:
```agda
{-|
Dual theorem to: more-expressive-by-soundness.
-}
more-expressive-by-completeness : ∀ {L M : VariabilityLanguage V}
  → Complete L
  → Sound M
  → Incomplete M
    -------------
  → L ≻ M
more-expressive-by-completeness L-comp M-sound M-incomp =
    expressiveness-by-completeness-and-soundness L-comp M-sound
  , less-expressive-from-completeness L-comp M-incomp

{-|
Dual theorem to: more-expressive-by-completeness.
-}
more-expressive-by-soundness : ∀ {L M : VariabilityLanguage V}
  → Sound L
  → Complete M
  → Unsound M
    -----------
  → M ≻ L
more-expressive-by-soundness L-sound M-comp M-unsound =
    expressiveness-by-completeness-and-soundness M-comp L-sound
  , less-expressive-from-soundness L-sound M-unsound
```

There cannot exist sound languages that are more expressive than complete languages.
Since complete languages can denote any element in their semantic domain,
and sound languages can only denote such elements, there cannot be anything denoted
by the sound language that cannot be denoted by the complete language.
Below, we provide two alternative formulations of the same theorem.
(The proof for the second theorem uses the first theorem.)

```agda
complete-is-most-expressive : ∀ {L : VariabilityLanguage V}
  → Complete L
    ----------------
  → ∄[ M ] (Sound M × M ≻ L)
complete-is-most-expressive L-comp (M , M-sound , M≽L , L⋡M) =
  L⋡M (expressiveness-by-completeness-and-soundness L-comp M-sound)

complete-is-most-expressive' : ∀ {L : VariabilityLanguage V}
  → Sound L
    ----------------
  → ∄[ M ] (Complete M × L ≻ M)
complete-is-most-expressive' {L} L-sound (M , M-comp , L≻M) = complete-is-most-expressive M-comp (L , L-sound , L≻M)
```
