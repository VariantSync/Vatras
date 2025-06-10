## Properties

We now prove completeness and soundness of clone-and-own.
These proofs will form the basis for proving these properties for other languages as well.

```
open import Vatras.Framework.Definitions using (𝕍; 𝔸)
module Vatras.Lang.VariantList.Properties (V : 𝕍) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (_∷_; [])
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Vatras.Data.EqIndexedSet using (_⊆[_]_; _≅_; ≅[]→≅)
open import Vatras.Util.Nat.AtLeast using (cappedFin)
open import Vatras.Framework.VariantGenerator V using (VariantGenerator; remove-first)
open import Vatras.Framework.Relation.Configuration V using (_∋_⊢_≣ⁱ_)
open import Vatras.Framework.Properties.Soundness V using (Sound)
open import Vatras.Framework.Properties.Completeness V using (Complete)
open import Vatras.Lang.VariantList V using (VariantList; Configuration; ⟦_⟧; VariantListL)
```

### Completeness

To prove completeness, we have to show that lists of variants can express any variant generator.

```agda
private
  variable
    n : ℕ
    A : 𝔸
    e : VariantList A

-- rules for translating a variant generator to a list of variants
infix 3 _⊢_⟶_
data _⊢_⟶_ : ∀ (n : ℕ) → VariantGenerator A n → VariantList A → Set₁ where
  -- a singleton set is translated to a singleton list
  E-zero : ∀ {A} {V : VariantGenerator A zero}
      ------------------------
    → zero ⊢ V ⟶ V zero ∷ []

  {-|
  For a set V with more than one variant, we:
  - put the first variant into our list
  - remove that first variant from our set of variants
  - translate the rest recursively.
  -}
  E-suc : ∀ {V : VariantGenerator A (suc n)}
    → n ⊢ remove-first A V ⟶ e
      -------------------------------
    → suc n ⊢ V ⟶ V zero ∷ List⁺.toList e

{-| Proof that the encoding is deterministic -}
determinism : ∀ {e₁ e₂ : VariantList A} {V : VariantGenerator A n}
  → n ⊢ V ⟶ e₁
  → n ⊢ V ⟶ e₂
    -----------------
  → e₁ ≡ e₂
determinism E-zero E-zero = refl
determinism (E-suc l) (E-suc r) rewrite determinism l r = refl

-- smart constructor for totality proofs
-- makes the implicit result expression e explicit
return : ∀ {V : VariantGenerator A n}
  →         n ⊢ V ⟶ e
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
return {e = e} ⟶e = e , ⟶e

{-| Proof that the encoding is total and thus can be computed. -}
total :
  ∀ (V : VariantGenerator A n)
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
total {n = zero}  vs = return E-zero
total {n = suc n} vs = return (E-suc (proj₂ (total (remove-first _ vs))))

{-| Encodes a set of variants into a list of variants. -}
encode : VariantGenerator A n → VariantList A
encode = proj₁ ∘ total

-- translate configs

vl-conf : Fin (suc n) → Configuration
vl-conf i = Fin.toℕ i

vl-fnoc : Configuration → Fin (suc n)
vl-fnoc c = cappedFin c

-- prove preservation of the encoding

preserves-∈ : ∀ {V}
  → n ⊢ V ⟶ e
    ---------------------
  → V ⊆[ vl-conf ] ⟦ e ⟧
preserves-∈ E-zero    zero = refl

preserves-∈ (E-suc _) zero = refl
preserves-∈ (E-suc ⟶e) (suc i) = preserves-∈ ⟶e i

preserves-∋ : ∀ {V}
  → n ⊢ V ⟶ e
    ---------------------
  → ⟦ e ⟧ ⊆[ vl-fnoc ] V
preserves-∋ E-zero      zero   = refl
preserves-∋ E-zero     (suc _) = refl
preserves-∋ (E-suc  _)  zero   = refl
preserves-∋ (E-suc ⟶e) (suc c) = preserves-∋ ⟶e c

preserves : ∀ {V}
  → n ⊢ V ⟶ e
    ----------
  → V ≅ ⟦ e ⟧
preserves encoding = ≅[]→≅ (preserves-∈ encoding , preserves-∋ encoding)

-- final completeness proof
VariantList-is-Complete : Complete VariantListL
VariantList-is-Complete vs =
  let e , derivation = total vs
  in  e , preserves derivation
```

### Soundness

We can use a trick to prove soundness by reusing the above definitions for completeness.
The trick is that `⟦ e ⟧ ∘ vl-conf` denotes a variant generator because it takes a `Fin (suc n)` as input and produces a variant.
We are then left to prove that this variant generator exactly denotes the expression in e which is almost true by definition.
It just requires playing with the configuration translation functions a bit, and to prove
that `vl-conf` is the (semantic) inverse of `vl-fnoc`.

```agda
-- vl-conf is inverse to vl-fnoc w.r.t. semantic equivalence of configurations.
inverse : ∀ {A} (c : Configuration) (e : VariantList A) → VariantListL ∋ e ⊢ vl-conf {List⁺.length e} (vl-fnoc c) ≣ⁱ c
inverse zero e = refl
inverse (suc c) (_ ∷ []) = refl
inverse (suc c) (_ ∷ y ∷ ys) = inverse c (y ∷ ys)

VariantList-is-Sound : Sound VariantListL
VariantList-is-Sound e =
    List⁺.length e
  , ⟦ e ⟧ ∘ vl-conf
  , (λ i → vl-conf i , refl)
  , (λ i → vl-fnoc i , sym (inverse i e))
```
