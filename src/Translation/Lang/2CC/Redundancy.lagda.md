This module defines an intra-language compiler for binary
choice calculus that eliminates any redundant choices.
If a choice is nested somewhere below a choice with the same
dimensions, the inner choice effectively, cannot be configured anymore.
This phenomenon is known as "choice domination" in the choice calculus
papers.
Example:

> D ⟨ l , D ⟨ x , y ⟩ ⟩

Here, `x` is dead because in order to reach it, we would have to configure
the dimension `D` to be `false` (to go right in the outer choice) and then
to `true` (to go left in the inner choice) which is not legal.
We can hence simplify this choice to:

> D ⟨ l , y ⟩

which is exactly what happens in this module.

TODO: The compiler currently is forgetful. While it produces an expression
      without dead choices, it does not generate a proof (or typing) for the
      resulting expression that it indeed has this property.
-}
```agda
open import Framework.Definitions using (𝔸; 𝔽)
open import Relation.Binary.Definitions using (DecidableEquality)
module Translation.Lang.2CC.Redundancy (Dimension : 𝔽) (_==_ : DecidableEquality Dimension) where

open import Function using (id)
open import Size using (Size; ∞)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; map)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_)
open Eq.≡-Reasoning

open import Framework.Compiler using (LanguageCompiler)
open import Framework.Variants as V using (Rose)
open import Util.AuxProofs using (true≢false)

open import Data.EqIndexedSet using (≗→≅[]; ≅[]-sym)

open import Lang.2CC
```

A scope remembers any dominating outer choices.
When traversing a `2CC` expression, the scope keeps track
of any visited choices above the current expression and remembers
whether the outer choice must be configured to true or false in
order to reach this expression.
To type theory / PL theory people, a scope may appear as an environment Γ.
```agda
Scope : Set
Scope = Dimension → Maybe Bool

{-|
Refines a scope by adding a new value for a given dimension.
-}
refine : Scope → Dimension → Bool → Scope
refine scope D b D' with D == D'
refine scope D b D' | yes _ = just b
refine scope D b D' | no _ = scope D'

{-|
Recursively eliminates dominated choices assuming the given outer scope.
-}
eliminate-redundancy-in : ∀ {i : Size} {A : 𝔸} → Scope → 2CC Dimension i A → 2CC Dimension ∞ A
eliminate-redundancy-in scope (a -< es >-) = a -< map (eliminate-redundancy-in scope) es >-
eliminate-redundancy-in scope (D ⟨ l , r ⟩) with scope D
... | just true  = eliminate-redundancy-in scope l
... | just false = eliminate-redundancy-in scope r
... | nothing    = D ⟨ eliminate-redundancy-in (refine scope D true ) l
                    , eliminate-redundancy-in (refine scope D false) r
                    ⟩

{-|
Recursively eliminates dominated choices.
-}
eliminate-redundancy : ∀ {i : Size} {A : 𝔸} → 2CC Dimension i A → 2CC Dimension ∞ A
eliminate-redundancy = eliminate-redundancy-in (λ _ → nothing)

{-|
Proof that eliminating dominated choices does not change semantics.
-}
preserves-≗ : ∀ {i : Size} {A : 𝔸}
  → (scope : Scope)
  → (c : Configuration Dimension)
  → (∀ {D : Dimension} {b : Bool} → scope D ≡ just b → c D ≡ b)
  → (e : 2CC Dimension i A)
  → ⟦ eliminate-redundancy-in scope e ⟧ c ≡ ⟦ e ⟧ c
preserves-≗ scope c p (a -< cs >-) =
    ⟦ eliminate-redundancy-in scope (a -< cs >-) ⟧ c
  ≡⟨⟩
    ⟦ a -< map (eliminate-redundancy-in scope) cs >- ⟧ c
  ≡⟨⟩
    a V.-< map (λ e → ⟦ e ⟧ c) (map (eliminate-redundancy-in scope) cs) >-
  ≡⟨ Eq.cong (a V.-<_>-) (List.map-∘ cs) ⟨
    a V.-< map (λ e → ⟦ eliminate-redundancy-in scope e ⟧ c) cs >-
  ≡⟨ Eq.cong (a V.-<_>-) (List.map-cong (λ e → preserves-≗ scope c p e) cs) ⟩
    a V.-< map (λ e → ⟦ e ⟧ c) cs >-
  ≡⟨⟩
    ⟦ a -< cs >- ⟧ c
  ∎
preserves-≗ scope c p (D ⟨ l , r ⟩) with scope D in scope-D
preserves-≗ scope c p (D ⟨ l , r ⟩) | just true with c D in c-D
preserves-≗ scope c p (D ⟨ l , r ⟩) | just true | false = ⊥-elim (true≢false (p scope-D) c-D)
preserves-≗ scope c p (D ⟨ l , r ⟩) | just true | true = preserves-≗ scope c p l
preserves-≗ scope c p (D ⟨ l , r ⟩) | just false with c D in c-D
preserves-≗ scope c p (D ⟨ l , r ⟩) | just false | false = preserves-≗ scope c p r
preserves-≗ scope c p (D ⟨ l , r ⟩) | just false | true = ⊥-elim (true≢false c-D (p scope-D))
preserves-≗ scope c p (D ⟨ l , r ⟩) | nothing with c D in c-D
preserves-≗ scope c p (D ⟨ l , r ⟩) | nothing | true = preserves-≗ (refine scope D true) c lemma l
  where
  lemma : ∀ {D' : Dimension} {b : Bool} → refine scope D true D' ≡ just b → c D' ≡ b
  lemma {D' = D'} p' with D == D'
  lemma {b = true} p' | yes refl = c-D
  lemma p' | no D≢D' = p p'
preserves-≗ scope c p (D ⟨ l , r ⟩) | nothing | false = preserves-≗ (refine scope D false) c lemma r
  where
  lemma : ∀ {D' : Dimension} {b : Bool} → refine scope D false D' ≡ just b → c D' ≡ b
  lemma {D' = D'} p' with D == D'
  lemma {b = false} p' | yes refl = c-D
  lemma p' | no D≢D' = p p'

{-|
An intra-language compiler for eliminating redundant choices.
-}
Redundancy-Elimination : LanguageCompiler (2CCL Dimension) (2CCL Dimension)
Redundancy-Elimination = record
  { compile = eliminate-redundancy
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = λ e → ≅[]-sym (≗→≅[] λ c → preserves-≗ (λ _ → nothing) c (λ where ()) e)
  }
```
