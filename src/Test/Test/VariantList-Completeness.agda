{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Test.Test.VariantList-Completeness where

open import Level using (Level; 0ℓ; Lift; lift) renaming (suc to lsuc)

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to f-zero; suc to f-suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Util.Named using (get)
open import Test.Examples.Variants
open import Test.UnitTest

open import Framework.Definitions using (VMap)
open import Lang.VariantList as VL using (Configuration; ⟦_⟧)

test-encode-conf : ∀ {A n} → Fin (suc n) → UnitTest (VMap A n)
test-encode-conf {A} i 𝕍 =
  let open VL.Complete A using (encode; conf)
   in ⟦ encode 𝕍 ⟧ (conf i) ≡ 𝕍 i

test-encode-fnoc : ∀ {A n} → Configuration → UnitTest (VMap A n)
test-encode-fnoc {A} c 𝕍 =
  let open VL.Complete A using (encode; fnoc)
   in ⟦ encode 𝕍 ⟧ c ≡ 𝕍 (fnoc c)

-- is there a better way to write these shortcuts?
0f : ∀ {n} → Fin (suc n)
0f = f-zero
1f : ∀ {n} → Fin (suc (suc n))
1f = f-suc 0f
2f : ∀ {n} → Fin (suc (suc (suc n)))
2f = f-suc 1f

-- conf

test-encode-conf-𝕍-123-0 : ForExample (test-encode-conf 0f) 𝕍-123
test-encode-conf-𝕍-123-0 = refl

test-encode-conf-𝕍-123-1 : ForExample (test-encode-conf 1f) 𝕍-123
test-encode-conf-𝕍-123-1 = refl

test-encode-conf-𝕍-123-2 : ForExample (test-encode-conf 2f) 𝕍-123
test-encode-conf-𝕍-123-2 = refl

test-encode-conf-𝕍-lr-0 : ForExample (test-encode-conf 0f) 𝕍-lr
test-encode-conf-𝕍-lr-0 = refl

test-encode-conf-𝕍-lr-1 : ForExample (test-encode-conf 1f) 𝕍-lr
test-encode-conf-𝕍-lr-1 = refl

-- fnoc

test-encode-fnoc-𝕍-123-0 : ForExample (test-encode-fnoc 0) 𝕍-123
test-encode-fnoc-𝕍-123-0 = refl

test-encode-fnoc-𝕍-123-1 : ForExample (test-encode-fnoc 1) 𝕍-123
test-encode-fnoc-𝕍-123-1 = refl

test-encode-fnoc-𝕍-123-2 : ForExample (test-encode-fnoc 2) 𝕍-123
test-encode-fnoc-𝕍-123-2 = refl

test-encode-fnoc-𝕍-lr-0 : ForExample (test-encode-fnoc 0) 𝕍-lr
test-encode-fnoc-𝕍-lr-0 = refl

test-encode-fnoc-𝕍-lr-1 : ForExample (test-encode-fnoc 1) 𝕍-lr
test-encode-fnoc-𝕍-lr-1 = refl
