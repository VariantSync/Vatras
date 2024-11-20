```
open import Vatras.Framework.Definitions using (𝔽)
module Vatras.Lang.CCC.Encode {Dimension : 𝔽} where

open import Data.List as List using (List; []; _∷_)

open import Size using (∞)
open import Data.Unit using (⊤; tt)
open import Data.List.Properties using (map-∘; map-id; map-cong)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; irrelevant-index-≅)
open import Vatras.Framework.Variants as V using (Rose; Variant-is-VL; VariantEncoder)
open import Vatras.Framework.Relation.Function using (_⇔_; to; from)
open import Vatras.Framework.VariabilityLanguage using (Semantics; Config)
open import Vatras.Lang.CCC Dimension
```

## Encoding Variants

Core choice calculus can express singleton systems as well (i.e., domains in which there is only exactly one variant).
Such behavior is implemented in terms of [variant encoders](../Framework/Variants.agda).
We can encode a variant in core choice calculus by using only the artifact constructor and no choices.
```agda
{-|
Encode a rose tree in a core choice calculus expression.
-}
encode : ∀ {i} {A} → Rose i A → CCC ∞ A
encode (a V.-< cs >-) = a -< List.map encode cs >-

{-|
Translating configurations is trivial because their values never matter.
We can do anything here.
-}
confs : ⊤ ⇔ Config CCCL
confs = record
  { to = λ where tt _ → 0
  ; from = λ _ → tt
  }

{-|
Correctness proof of the encoding: We always get our encoded variant back.
-}
ccc-encode-idemp : ∀ {A} (v : Rose ∞ A) → (c : Configuration) → ⟦ encode v ⟧ c ≡ v
ccc-encode-idemp {A} v@(a V.-< cs >-) c =
  begin
    ⟦ encode v ⟧ c
  ≡⟨⟩
    a V.-< List.map (λ x → ⟦ x ⟧ c) (List.map encode cs) >-
  ≡⟨ Eq.cong (a V.-<_>-) (map-∘ cs) ⟨
    a V.-< List.map (λ x → ⟦ encode x ⟧ c) cs >-
  ≡⟨ Eq.cong (a V.-<_>-) (go cs) ⟩
    v
  ∎
  where
  open Eq.≡-Reasoning

  go : (cs' : List (Rose ∞ A)) → List.map (λ c' → ⟦ encode c' ⟧ c) cs' ≡ cs'
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

encoder : VariantEncoder (Rose ∞) CCCL
encoder = record
  { compile = encode
  ; config-compiler = λ _ → confs
  ; preserves = preserves
  }
```
