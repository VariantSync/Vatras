open import Vatras.Framework.Definitions
open import Vatras.Data.EqIndexedSet

module Vatras.Translation.Lang.VariantList-to-VariationTree (F : 𝔽) (f : F) where

import Data.Bool as Bool
open Bool using (if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _∷⁺_; _++⁺_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≡ᵇ_; _+_; _≤_; _>_; s≤s; z≤n; _∸_; _≤ᵇ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; m≤n+m; ≤-refl; m≤n⇒m≤n+o; ≡⇒≡ᵇ; n∸n≡0)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; sym; cong)
open Eq.≡-Reasoning
open import Function using (_∘_; _$_; id)
open import Axiom.Extensionality.Propositional using (Extensionality)

Numbered : Set → Set
Numbered F = F × ℕ

+-Numbered : ∀ {F} → ℕ → Numbered F → Numbered F
+-Numbered n (g , i) = (g , n + i)

open import Vatras.Framework.Variants using (Forest; Rose; _-<_>-; rose-leaf; Variant-is-VL; encode-idemp)
open import Vatras.Data.Prop using (var)
open import Vatras.Lang.VariationTree.Encode (Numbered F)
-- open import Vatras.Lang.VariantList Forest using (VariantList)
open import Vatras.Lang.All.Fixed F Forest
open VariantList using (VariantList; VariantListL)

open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Util.List using (find-or-last)

≤-sucʳ : ∀ {m n} → m ≤ n → m ≤ suc n
≤-sucʳ z≤n = z≤n
≤-sucʳ (s≤s leq) = s≤s (≤-sucʳ leq)

-- TODO: contribute these functions to stl
≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ Bool.true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≡ᵇ-> : ∀ {m n} → m > n → (m ≡ᵇ n) ≡ Bool.false
≡ᵇ-> {.(suc _)} {zero} (s≤s x) = refl
≡ᵇ-> {suc m} {suc n} (s≤s x) = ≡ᵇ-> x

≡ᵇ-no : ∀ i n → (suc i + n ≡ᵇ n) ≡ Bool.false
≡ᵇ-no i n = ≡ᵇ-> (s≤s (m≤n+m n i))

module _ where
  open import Vatras.Lang.VariationTree (Numbered F)

  translate' : ∀ {A} → ℕ → Forest A → List (Forest A) → List (UnrootedVT A)
  translate' n x []       = encode-forest x
  translate' n x (y ∷ ys) =
    -- List.length (y ∷ ys) is the number of variants left in the else branch
    if[ var (f , n) ]then[ -- really suc
      encode-forest x
    ]else[
      translate' (suc n) y ys
    ] ∷ []

  -- translateʳ : ∀ {A} → VariantList A → VT A
  -- translateʳ (x ∷ xs) = if-true[ translate' x xs ]

  reverse⁺ : ∀ {ℓ} {B : Set ℓ} → List⁺ B → List⁺ B
  reverse⁺ (x ∷ xs) = List.reverse xs ++⁺ (x ∷ [])

  translate : ∀ {A} → VariantList A → VT A
  -- translate xs = translateʳ (reverse⁺ xs)
  translate (x ∷ xs) = if-true[ translate' zero x xs ]

  {-
      conf : ∀ {n} → Fin n → Conf (Numbered F)
      conf Fin.zero    (x , j) = Bool.false
      conf (Fin.suc i) (x , j) with toℕ (Fin.suc i) ≟ j
      ... | yes _ = Bool.true
      ... | no  _ = Bool.false
  -}
  conf : ℕ → Conf
  conf i (_ , j) = i ≡ᵇ j

  -- fnoc : ∀ {n} → Fin n → Conf (Numbered F) → Fin n
  -- fnoc Fin.zero     c = Fin.zero
  -- fnoc (Fin.suc j)  c with c (x , toℕ (Fin.suc j))
  -- ... | Bool.true  = Fin.suc j
  -- ... | Bool.false = inject₁ (fnoc j c)
  -- 
  -- fnoc : ℕ → Conf → ℕ
  -- fnoc zero c = zero
  -- fnoc (suc j) c with c (f , suc j)
  -- ... | Bool.true  = suc j
  -- ... | Bool.false = fnoc j c
  -- fnoc : (max i : ℕ) → i ≤ max → Conf → ℕ
  -- fnoc max .zero z≤n c = {!!}
  -- fnoc .(suc _) .(suc _) (s≤s ge) c = {!!}
  -- fnoc' : (max i : ℕ) → i ≤ max → Conf → ℕ
  -- fnoc' max zero z≤n c =
  --   if c (f , zero)
  --   then zero
  --   else max
  -- fnoc' (suc max) (suc i) (s≤s leq) c =
  --   if c (f , suc i)
  --   then suc i
  --   else fnoc' (suc max) i (≤-sucʳ leq) c
  fnoc' : (max i : ℕ) → Conf → ℕ
  fnoc' max zero c =
    if c (f , zero)
    then zero
    else max
  fnoc' max (suc i) c =
    let rec = fnoc' max i c
    in
    if (rec ≡ᵇ max) then
      if c (f , suc i)
      then suc i
      else max
    else rec

  -- fnoci : (max i : ℕ) → i ≤ max → Conf → ℕ
  -- fnoci max zero z≤n c = max
  -- fnoci (suc max) (suc i) (s≤s i≤max) c =
  --   if c (f , max ∸ i)
  --   then max ∸ i
  --   else fnoci (suc max) i (≤-sucʳ i≤max) c
  fnoci : (max i : ℕ) → Conf → ℕ
  fnoci max zero c = max
  fnoci max (suc i) c =
    if c (f , max ∸ suc i)
    then max ∸ suc i
    else fnoci max i c

  -- fnoci : (max i : ℕ) → i ≤ max → Conf → ℕ
  -- fnoci max i leq c with max ≟ i
  -- fnoci max .max leq c | yes refl = max
  -- fnoci max i leq c | no asd =
  --   if c (f , i)
  --   then i
  --   else fnoci max (suc i) {!!} c

  -- {-# TERMINATING #-}
  -- fnoc' : (max i : ℕ) → Conf → ℕ
  -- fnoc' max i c =
  --   if i ≤ᵇ max
  --   then if c (f , i)
  --        then i
  --        else fnoc' max (suc i) c
  --   else max

  fnoc : (max : ℕ) → Conf → ℕ
  fnoc max = fnoci max max
  -- fnoc max = fnoc' max max
  -- fnoc max = fnoc' max max ≤-refl
  -- fnoc max = fnoc' max zero

  fnoc-offset : ℕ → Conf → Conf
  fnoc-offset n c = c ∘ +-Numbered n

  {- fnoc lemmata: -}

  -- fnoc-offset does nothing at zero
  fnoc-offset-id : ∀ (c : Conf) → fnoc-offset zero c ≗ c
  fnoc-offset-id c x = refl

  -- When there are multiple places at which a Conf returns true, then fnoc picks the smallest place.
  -- fnoc-smallest : ∀ (c : Conf) (max n : ℕ)
  --   → (leq : n ≤ max)
  --   → c (f , n) ≡ Bool.true
  --   → fnoci max n leq c ≤ n
  -- fnoc-smallest c max zero z≤n x = {!!}
  -- fnoc-smallest c max (suc n) leq x = {!!}


module Test where
  open import Vatras.Lang.VariationTree
  ⟦_⟧ₜ = ⟦_⟧ (Numbered F)

  ℕ𝔸 : 𝔸
  ℕ𝔸 = ℕ , _≟_

  vtleaf : ∀ {F A} → atoms A → UnrootedVT F A
  vtleaf a = a -< [] >-

  -- some tests first
  vl1 : VariantList ℕ𝔸
  vl1 =
    (rose-leaf 0 ∷ []) ∷
    (rose-leaf 1 ∷ []) ∷
    (rose-leaf 2 ∷ []) ∷
    []

  tr-vl1 : translate vl1 ≡
    if-true[
      if[ var (f , 0) ]then[
        vtleaf 0 ∷ []
      ]else[
        if[ var (f , 1) ]then[
          vtleaf 1 ∷ []
        ]else[
          vtleaf 2 ∷ []
        ] ∷ []
      ] ∷ []
    ]
  tr-vl1 = refl

  cn : ℕ → Conf (Numbered F)
  cn n (_ , i) = i ≡ᵇ n

  ctrue : Conf (Numbered F)
  ctrue _ = Bool.true

  cfalse : Conf (Numbered F)
  cfalse _ = Bool.false

  sem-vl1 : ⟦ translate vl1 ⟧ₜ (cn 0) ≡ VariantList.⟦ vl1 ⟧ (fnoc (List⁺.length vl1) (cn 0))
  sem-vl1 = refl

  testi : ∀ {A} (x : Forest A) (xs : List (Forest A)) (n : ℕ) (c : Conf (Numbered F)) → Set₁
  testi x xs n c = configure-all (Numbered F) c (translate' n x xs) ≡ VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) (fnoc-offset n c))

  testii = testi {ℕ𝔸} (rose-leaf 0 ∷ []) ((rose-leaf 1 ∷ []) ∷ (rose-leaf 2 ∷ []) ∷ [])

  bar0 : testii zero ctrue
  bar0 = refl

  bar1 : testii 1 ctrue
  bar1 = refl

  bar2 : testii 2 ctrue
  bar2 = refl

  baz0 : testii zero cfalse
  baz0 = refl

  baz1 : testii 1 cfalse
  baz1 = refl

  baz2 : testii 2 cfalse
  baz2 = refl

  foo0-0 : testii zero (cn 0)
  foo0-0 = refl

  foo0-1 : testii zero (cn 1)
  foo0-1 = refl

  foo0-2 : testii zero (cn 2)
  foo0-2 = refl

  foo1-0 : testii 1 (cn 0)
  foo1-0 = refl

  foo1-1 : testii 1 (cn 1)
  foo1-1 = refl

  foo1-2 : testii 1 (cn 2)
  foo1-2 = refl

  foo2-0 : testii 2 (cn 0)
  foo2-0 = refl

  foo2-1 : testii 2 (cn 1)
  foo2-1 = refl

  foo2-2 : testii 2 (cn 2)
  foo2-2 = refl

module Preservation (A : 𝔸) where
  open import Vatras.Lang.VariationTree (Numbered F)

  translate'-preserves-conf : ∀ (x : Forest A) (xs : List (Forest A)) (n : ℕ) (i : ℕ) →
    configure-all (conf (i + n)) (translate' n x xs ) ≡ VariantList.⟦ x ∷ xs ⟧ i
  translate'-preserves-conf x [] n i =
    begin
      configure-all (conf (i + n)) (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder (conf (i + n)) x ⟩
      x
    ≡⟨⟩
      VariantList.⟦ x ∷ [] ⟧ i
    ∎
  translate'-preserves-conf x (y ∷ ys) n zero rewrite ≡ᵇ-refl n =
    begin
      configure-all (conf n) (encode-forest x) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all (conf n) (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder (conf n) x ⟩
      x
    ≡⟨⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧ zero
    ∎
  translate'-preserves-conf x (y ∷ ys) n (suc i) rewrite ≡ᵇ-no i n =
    begin
      configure-all (conf (suc i + n)) (translate' (suc n) y ys) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all (conf (suc i + n)) (translate' (suc n) y ys)
    ≡⟨ cong (λ eq → configure-all (conf eq) (translate' (suc n) y ys)) (+-suc i n) ⟨
      configure-all (conf (i + suc n)) (translate' (suc n) y ys)
    ≡⟨ translate'-preserves-conf y ys (suc n) i ⟩
      VariantList.⟦ y ∷ ys ⟧ i
    ≡⟨⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧ (suc i)
    ∎

  preserves-⊆ : ∀ (l : VariantList A)
    → VariantList.⟦ l ⟧ ⊆[ conf ] ⟦ translate l ⟧
  preserves-⊆ (x ∷ xs) i = sym $
    begin
      ⟦ translate (x ∷ xs) ⟧ (conf i)
    ≡⟨⟩
      configure-all (conf i) (translate' zero x xs)
    ≡⟨ cong (λ eq → configure-all (conf eq) (translate' zero x xs)) (+-identityʳ i) ⟨
      configure-all (conf (i + zero)) (translate' zero x xs)
    ≡⟨ translate'-preserves-conf x xs zero i ⟩
      VariantList.⟦ x ∷ xs ⟧ i
    ∎

  len+ = List⁺.length
  asd : ∀ (x : Forest A) (xs : List⁺ (Forest A)) (n : ℕ) (c : Conf) →
        VariantList.⟦      xs ⟧ (fnoci (len+       xs)  (len+ xs) (fnoc-offset (suc n) c))
      ≡ VariantList.⟦ x ∷⁺ xs ⟧ (fnoci (len+ (x ∷⁺ xs)) (len+ xs) (fnoc-offset      n  c))
  asd x (y ∷ []) zero c = {!!}
  asd x (y ∷ x₁ ∷ ys) zero c = {!!}
  asd x xs (suc n) c = {!!}


  translate'-preserves-fnoc : ∀ (x : Forest A) (xs : List (Forest A)) (n : ℕ) (c : Conf) →
      configure-all c (translate' n x xs)
    ≡ VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) (fnoc-offset n c))
  translate'-preserves-fnoc x [] n c = encode-idemp Forest A encoder c x
  translate'-preserves-fnoc x (y ∷ ys) n c with c (f , n) in eq
  ... | Bool.true rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq =
    begin
      configure-all c (encode-forest x) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all c (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder c x ⟩
      x
    ∎
  ... | Bool.false rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq =
    begin
      configure-all c (translate' (suc n) y ys) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all c (translate' (suc n) y ys)
    ≡⟨ translate'-preserves-fnoc y ys (suc n) c ⟩
      VariantList.⟦     y ∷ ys ⟧
        (fnoc  (List⁺.length (y ∷ ys)) (fnoc-offset (suc n) c))
    ≡⟨⟩
      VariantList.⟦     y ∷ ys ⟧
        (fnoci (List⁺.length (    y ∷ ys)) (List⁺.length (y ∷ ys)) (fnoc-offset (suc n) c))
    ≡⟨ asd x (y ∷ ys) n c ⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧
        (fnoci (List⁺.length (x ∷ y ∷ ys)) (List⁺.length (y ∷ ys)) (fnoc-offset n c))
    --   VariantList.⟦ x ∷ y ∷ ys ⟧ (fnoc (List⁺.length (x ∷ y ∷ ys)) (fnoc-offset n c))
    ∎

  preserves-⊇ : ∀ (l : VariantList A)
    → ⟦ translate l ⟧ ⊆[ fnoc (List⁺.length l) ] VariantList.⟦ l ⟧
  preserves-⊇ (x ∷ xs) c =
    begin
      ⟦ translate (x ∷ xs) ⟧ c
    ≡⟨⟩
      configure-all c (translate' zero x xs)
    ≡⟨ translate'-preserves-fnoc x xs zero c ⟩
      VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) (fnoc-offset zero c))
    -- ≡⟨ {!!} ⟩
      -- find-or-last (fnoc (List⁺.length (x ∷ xs)) c) (x ∷ xs)
    ≡⟨ cong
       (λ eq → VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) eq))
       (ext (fnoc-offset-id c)) ⟩
      VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) c)
    ∎
    where
      open import Level using (0ℓ)
      postulate
        ext : Extensionality 0ℓ 0ℓ
