open import Vatras.Framework.Definitions using (𝔽)
module Vatras.Lang.2CC.Encode {Dimension : 𝔽} where

open import Data.List as List using (List; []; _∷_)

open import Size using (∞)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.List.Properties using (map-∘; map-id; map-cong)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; irrelevant-index-≅)
open import Vatras.Framework.Variants as V using (Rose; Variant-is-VL; VariantEncoder)
open import Vatras.Framework.Relation.Function using (_⇔_; to; from)
open import Vatras.Framework.VariabilityLanguage using (Semantics; Config)
open import Vatras.Lang.2CC Dimension

encode : ∀ {i} {A} → Rose i A → 2CC ∞ A
encode (a V.-< cs >-) = a -< List.map encode cs >-

confs : ⊤ ⇔ Config 2CCL
confs = record
  { to = λ where tt _ → false
  ; from = λ _ → tt
  }

2cc-encode-idemp : ∀ {A} (v : Rose ∞ A) → (c : Configuration) → ⟦ encode v ⟧ c ≡ v
2cc-encode-idemp {A} v@(a V.-< cs >-) c =
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
  go (c' ∷ cs') = Eq.cong₂ _∷_ (2cc-encode-idemp c' c) (go cs')

preserves : ∀ {A} → (v : Rose ∞ A)
  → Semantics (Variant-is-VL (Rose ∞)) v ≅[ to confs ][ from confs ] ⟦ encode v ⟧
preserves {A} v = irrelevant-index-≅ v
  (λ { tt → refl })
  (2cc-encode-idemp v)
  (to confs)
  (from confs)

encoder : VariantEncoder (Rose ∞) 2CCL
encoder = record
  { compile = encode
  ; config-compiler = λ _ → confs
  ; preserves = preserves
  }
