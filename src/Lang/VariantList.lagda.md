# Lists of Variants are Also Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.VariantList where
```

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.NonEmpty using (List⁺; _∷_; toList; length; _⁺∷ʳ_; _∷ʳ_)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Definitions

open import Util.AuxProofs using (clamp)
open import Util.List using (lookup-clamped)
```

## Definitions

```agda
VariantList : VarLang
VariantList i A = List⁺ (Variant i A)

-- it would be nice if the confLang would be parameterized in expressions
Configuration : ConfLang
Configuration = ℕ

find : ∀ {A : Set} → List⁺ A → ℕ → A
find (x ∷ xs)        zero = x
find (x ∷ [])     (suc n) = x
find (x ∷ y ∷ ys) (suc n) = find (y ∷ ys) n

must-take-whats-left : ∀ {A : Set} {x : A}
 → (i : ℕ)
 → find (x ∷ []) i ≡ x
must-take-whats-left zero = refl
must-take-whats-left (suc i) = refl

-- ⟦_⟧ : ∀ {i : Size} {A : Domain} → VariantList i A → Configuration → Variant i A
⟦_⟧ : Semantics VariantList Configuration
⟦_⟧ = find

VariantListL : VariabilityLanguage
VariantListL = record
  { expression    = VariantList
  ; configuration = Configuration
  ; semantics     = ⟦_⟧
  }
```

## Properties

```agda
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; map₂)
open import Lang.Properties.Completeness
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; fromℕ<; fromℕ<″; inject₁; inject≤) renaming (_≟_ to _≟ᶠ_)

-- prove completeness via inference rules
module CI (A : Domain) where
  private
    variable
      n : ℕ
      V : VSet A n
      sV : VSet A (suc n)
      e e₁ e₂ : VariantList ∞ A

  -- data _>_ : ℕ → ℕ → Set where
  --   base : ∀ {c : ℕ}
  --     → suc c > zero
  --   grow : ∀ {c i : ℕ}
  --     → c > i
  --     → suc c > i

  -- fromℕ> : ∀ {c i : ℕ} → (c > i) → Fin c
  -- fromℕ> base = zero
  -- fromℕ> (grow c>i) = suc (fromℕ> c>i)

  -- infix 3 _⊢_∙_⟶_
  -- data _⊢_∙_⟶_ : (n : ℕ) → VSet A n → Fin (suc n) → VariantList ∞ A → Set where
  --   E-zero :
  --       ------------------------------
  --       n ⊢ vs ∙ zero ⟶ vs zero ∷ []

  --   E-suc : ∀ {i : Fin n}
  --     → n ⊢ vs ∙ inject₁ i ⟶ e
  --       ------------------------------------------
  --     → n ⊢ vs ∙ (suc i) ⟶ vs (suc i) ∷ toList e

  -- infix 3 _⊢_⟶_
  -- data _⊢_⟶_ : (n : ℕ) → VSet A n → VariantList ∞ A → Set where
  --   encode :
  --       n ⊢ vs ∙ (fromℕ n) ⟶ e
  --       ------------------------
  --     → n ⊢ vs ⟶ e

  infix 3 _⊢_⟶_
  data _⊢_⟶_ : (n : ℕ) → VSet A n → VariantList ∞ A → Set where
    E-zero :
        ------------------------------
        zero ⊢ V ⟶ V zero ∷ []

    E-suc :
        n ⊢ (forget-last sV) ⟶ e
        --------------------------------------------
      → suc n ⊢ sV ⟶ sV (fromℕ (suc n)) ∷ toList e

  determinism :
      n ⊢ V ⟶ e₁
    → n ⊢ V ⟶ e₂
      -----------------
    → e₁ ≡ e₂
  determinism E-zero E-zero = refl
  determinism (E-suc l) (E-suc r) rewrite determinism l r = refl

  -- smart constructor for totality proofs
  -- makes the implicit result expression e explicit
  return :
              n ⊢ V ⟶ e
      -------------------------
    → ∃[ e ] (n ⊢ V ⟶ e)
  return {e = e} ⟶e = e , ⟶e

  total :
    ∀ (V : VSet A n)
    → ∃[ e ] (n ⊢ V ⟶ e)
  total {n = zero}  vs = return E-zero
  total {n = suc n} vs = return (E-suc (proj₂ (total (forget-last vs))))

  -- translate configs
  open Data.Nat using (_∸_)

  conf : Fin (suc n) → Configuration
  conf {n = n} i = n ∸ toℕ i

  fnoc : Configuration → Fin (suc n)
  fnoc {n = n} i = {!!} -- actually the same as conf but fin juggling introduces much boilerplate

  open import Data.Multiset (VariantSetoid ∞ A) as Iso using (_∈_; _⊆_; _≅_)

  preserves-∈ :
    ∀ (c : Configuration)
    → n ⊢ V ⟶ e
      --------------------
    → ⟦ e ⟧ c ≡ V (fnoc c)
  preserves-∈ c ⟶e = {!!}

  preserves-∋ :
    ∀ (i : Fin (suc n))
    → n ⊢ V ⟶ e
      --------------------
    → V i ≡ ⟦ e ⟧ (conf i)
  preserves-∋ {n = zero} zero E-zero = refl
  preserves-∋ {n = suc n} i (E-suc ⟶e) = {!!}

  preserves-⊆ :
      n ⊢ V ⟶ e
      -----------
    → ⟦ e ⟧ ⊆ V
  preserves-⊆ ⟶e c = fnoc c , preserves-∈ c ⟶e

  preserves-⊇ :
      n ⊢ V ⟶ e
      -----------
    → V ⊆ ⟦ e ⟧
  preserves-⊇ ⟶e i = conf i , preserves-∋ i ⟶e

  preserves :
      n ⊢ V ⟶ e
      -----------
    → V ≅ ⟦ e ⟧
  preserves encoding = preserves-⊇ encoding , preserves-⊆ encoding

VariantList-is-complete-CI : Complete VariantListL
VariantList-is-complete-CI {A} vs =
  let open CI A
      e , derivation = total vs
   in (record { get = e }) , preserves derivation

module Completeness (A : Domain) where
  open import Data.Bool using (true; false)
  open Data.Nat using (_∸_; _≟_)

  open import Data.Nat.Properties using (n∸n≡0; ≤-trans; ≤-reflexive; m∸n≤m; m<n⇒m<1+n)
  open import Data.Fin.Properties using (fromℕ<-cong)
  open import Data.Multiset (VariantSetoid ∞ A) as Iso using (_∈_; _⊆_)
  open import Function using (case_of_)

  open import Relation.Nullary using (¬_; _because_; ofⁿ; ofʸ)
  open Eq using (inspect; [_])

  encode : (n : ℕ) → VSet A n → VariantList ∞ A
  encode    zero vs = vs zero ∷ []
  encode (suc n) vs = vs (fromℕ (suc n)) ∷ toList (encode n (forget-last vs)) -- ⁺∷ʳ vs (fromℕ (suc n))

  -- encode-⊆-n-zero :
  --   ∀ (n : ℕ)
  --   → (m : Fin (suc n))
  --   → (vs : VSet A n)
  --   → ⟦ encode n vs ⟧ ⊆ vs
  --   → ⟦ encode n vs ⟧ (toℕ m) ≡ vs m

  -- flubi :
  --   ∀ (n : ℕ)
  --   → (m : ℕ)
  --   → (m ≤ n)
  --   → (vs : VSet A (suc n))
  --   → ⟦ encode (suc n) vs ⟧ m ≡ ⟦ encode n (forget-last vs) ⟧ m
  -- flubi zero    zero x vs = refl
  -- flubi (suc n) zero x vs = refl
  -- flubi (suc n) (suc m) (s≤s m≤n) vs =
  --     ⟦ encode (suc (suc n)) vs ⟧ (suc m)
  --   ≡⟨⟩
  --     ⟦ encode (suc n) (forget-last vs) ⁺∷ʳ vs (fromℕ (suc (suc n))) ⟧ (suc m)
  --   ≡⟨ find-cong-r
  --        (vs (fromℕ (suc (suc n))))
  --        (encode (suc n) (forget-last vs))
  --        (suc m)
  --        (s≤s {!!})
  --        ⟩
  --     ⟦ encode (suc n) (forget-last vs) ⟧ (suc m)
  --   ∎
  --   where hypot : ⟦ encode (suc n) (forget-last vs) ⟧ m ≡ ⟦ encode n (forget-last (forget-last vs)) ⟧ m
  --         hypot = flubi n m m≤n (forget-last vs)

  -- m<n⇒1+m<1+n ∀ {m n : ℕ} → m < n → suc m < suc n
  -- m
  open Data.Nat using (_+_; _<″_; less-than-or-equal)
  ⊆-conf : -- conf to index
    ∀ (nvars : ℕ)
    → (c : Configuration)
      -------------------
    → Fin (suc nvars)
  ⊆-conf n-vars c = --n-vars ∸ c
    let config-ℕ : ℕ
        config-ℕ = n-vars ∸ c

        -- le1 : config-ℕ <″ suc n-vars
        -- le1 = record { k = c; proof = Eq.cong suc {!!}} --(m∸n≤m n-vars c)

        le : n-vars ∸ c ≤ n-vars
        le = m∸n≤m n-vars c

        lele : suc (n-vars ∸ c) ≤ suc n-vars
        lele = s≤s le
     in inject≤ (fromℕ config-ℕ) lele

  ⊇-conf :
    ∀ (nvars : ℕ)
    → (i : Fin (suc nvars))
    → Configuration
  ⊇-conf nvars i = nvars ∸ toℕ i

  -- {-# REWRITE ⊆-conf #-}
  ⊆-conf-zero-c : (c : Configuration) → ⊆-conf zero c ≡ zero
  ⊆-conf-zero-c  zero   = refl
  ⊆-conf-zero-c (suc _) = refl

  ⊆-conf-n-zero : (n : ℕ) → suc (fromℕ n) ≡ ⊆-conf (suc n) zero
  ⊆-conf-n-zero  zero   = refl
  ⊆-conf-n-zero (suc n) = Eq.cong suc (⊆-conf-n-zero n)

  ∸≡s∸ : ∀ (m n : ℕ) → m ∸ n ≡ suc m ∸ suc n
  ∸≡s∸ zero _ = refl
  ∸≡s∸ (suc m) zero = refl
  ∸≡s∸ (suc m) (suc n) = ∸≡s∸ m n

  inject₁-inject≤ : ∀ {m n} (m' : Fin m) (m≤n : m ≤ n)
    → inject₁ (inject≤ m' m≤n) ≡ inject≤ (inject₁ m') (s≤s m≤n)
  inject₁-inject≤ zero (s≤s m≤n) = refl
  inject₁-inject≤ (suc m') (s≤s m≤n) = Eq.cong suc (inject₁-inject≤ m' m≤n)

  ⊆-conf-inject : ∀ (n : ℕ) (c : Configuration)
    → inject₁ (⊆-conf n c) ≡ ⊆-conf (suc n) (suc c)
  ⊆-conf-inject zero zero    = refl
  ⊆-conf-inject zero (suc c) = refl
  ⊆-conf-inject (suc n) zero = Eq.cong suc (⊆-conf-inject n zero)
  ⊆-conf-inject (suc n) (suc c) =
    let sn = suc n
        sc = suc c
        ssn = suc sn
        ssc = suc sc
    in
      inject₁ (⊆-conf (suc n) (suc c))
    ≡⟨⟩
      inject₁ (inject≤ (fromℕ ( sn ∸  sc))  (s≤s (m∸n≤m  sn  sc)))
    ≡⟨ inject₁-inject≤ (fromℕ ( sn ∸  sc)) (s≤s (m∸n≤m  sn  sc)) ⟩
      inject≤ (inject₁ (fromℕ ( sn ∸  sc))) (s≤s (s≤s (m∸n≤m  sn  sc)))
    ≡⟨ {!!} ⟩
      inject≤          (fromℕ (ssn ∸ ssc))  (s≤s (m∸n≤m ssn ssc))
    ≡⟨⟩
      ⊆-conf (suc (suc n)) (suc (suc c))
    ∎

    -- with n ∸ c -- ⊆-conf (suc n) (suc c) | ⊆-conf-inject n c
  -- ... | x = ?
      -- let sn = suc n
      --     sc = suc c
      --     ssn = suc sn
      --     ssc = suc sc
      --     www : ssn ∸ ssc ≤ ssn
      --     www = (m∸n≤m (suc (suc n)) (suc (suc c)))
      --     wwww : ssn ∸ ssc < suc ssn
      --     wwww = s≤s www
      -- in
    -- case n ∸ c of λ
      -- { zero → {!!}
      -- inject₁ zero ≡⟨⟩
      -- zero         ≡⟨ {!!} ⟩
      -- -- ≡⟨ ? ⟩ -- (inject₁ (fromℕ< (s≤s (m∸n≤m n c)))) ≡⟨ ? ⟩
      -- -- suc (fromℕ< {zero} {sc} z≤n) ≡⟨⟩
      -- -- fromℕ< {ssn ∸ ssc} {ssc} (s≤s www) ≡⟨⟩
      -- inject≤ (fromℕ (ssn ∸ ssc)) (s≤s (m∸n≤m ssn ssc)) ≡⟨⟩
      -- ⊆-conf (suc (suc n)) (suc (suc c)) ∎
    -- ; (suc x) → {!!} }
  -- ... | suc n-c | y = {!!}
  -- ... | zero    =
      -- (inject₁ zero) ≡⟨ ⊆-conf-inject n c ⟩
      -- ⊆-conf
    -- inject₁ (⊆-conf sn sc) ≡⟨ {!!} ⟩
    -- fromℕ< (s≤s (m∸n≤m ssn ssc)) ≡⟨⟩
      -- ⊆-conf (suc (suc n)) (suc (suc c)) ∎
  -- ... | suc n∸c = {!!}
    -- let sn = suc n
    --     sc = suc c
    --     ssn = suc sn
    --     ssc = suc sc
    --  in
    -- inject₁ (⊆-conf sn sc) ≡⟨⟩
    -- inject₁ (⊆-conf sn sc) ≡⟨ {!!} ⟩
    -- fromℕ< (s≤s (m∸n≤m ssn ssc)) ≡⟨⟩
    -- ⊆-conf ssn ssc ∎

  encode-∈ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → ∀ (c : Configuration) → ⟦ encode n vs ⟧ c ≡ vs (⊆-conf n c)
  encode-∈ zero vs c =
    ⟦ vs zero ∷ [] ⟧ c     ≡⟨⟩
    find (vs zero ∷ []) c  ≡⟨ must-take-whats-left c ⟩
    vs zero                ≡⟨ Eq.sym (Eq.cong vs (⊆-conf-zero-c c)) ⟩
    vs (⊆-conf zero c)     ∎
  encode-∈ (suc n) vs   zero  = Eq.cong vs (⊆-conf-n-zero n)
  encode-∈ (suc n) vs (suc c) =
      ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (suc c)
    ≡⟨⟩
      ⟦ encode n (forget-last vs) ⟧ c
    ≡⟨ encode-∈ n (forget-last vs) c ⟩
      vs (inject₁ (⊆-conf n c))
    ≡⟨ Eq.cong vs (⊆-conf-inject n c) ⟩
      vs (⊆-conf (suc n) (suc c))
    ∎

  open import Level using (0ℓ)
  suc[m]≡suc[n]→m≡n : ∀ {m n : ℕ}
    → _≡_ {0ℓ} {ℕ} (suc m) (suc n)
      -------------
    → m ≡ n
  suc[m]≡suc[n]→m≡n refl = refl

  toℕ-cong : ∀ (n : ℕ) (m : Fin (suc n)) → (toℕ m) ≡ n → m ≡ (fromℕ n)
  toℕ-cong zero zero refl    = refl
  toℕ-cong (suc n) (suc m) x = Eq.cong suc (toℕ-cong n m (suc[m]≡suc[n]→m≡n x))

  encode-∋ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → ∀ (i : Fin (suc n)) → vs i ≡ ⟦ encode n vs ⟧ (⊇-conf n i)
  encode-∋ zero vs zero = refl
  encode-∋ (suc n) vs zero =
      vs zero
    ≡⟨ encode-∋ n (forget-last vs) zero ⟩
      ⟦ encode n (forget-last vs) ⟧ n
    ≡⟨⟩
      ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (suc n)
    ≡⟨⟩
      ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (⊇-conf (suc n) zero)
    ∎
  encode-∋ (suc n) vs (suc i) with n ∸ toℕ i | inspect (_∸ toℕ i) n
  ... | zero | [ n∸i=0 ] =
    let sem = ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧
    in
      vs (suc i)
      -- we need a guarantee that i ≤ n
      -- with Data.Nat.Properties.m∸n≡0⇒m≤n we can conclude that n ≤ i
      -- In conjunction we can conclude that i ≡ n
    ≡⟨ Eq.cong (λ eq → vs (suc eq)) {!!} ⟩ --flipped-p ⟩
      vs (suc (fromℕ n))
    ≡⟨⟩
      sem zero
    -- ≡⟨  Eq.sym (Eq.cong sem (n∸n≡0 n)) ⟩
    --   sem (n ∸ n)
    -- ≡⟨ Eq.cong (λ eq → sem (n ∸ eq)) p ⟩
    --   sem z
    ∎
    -- where
    --     ss : toℕ i ≡ n
    --     ss = Eq.sym p

    --     flipped-p : i ≡ fromℕ n
    --     flipped-p = toℕ-cong n i (Eq.sym p)
  ... | suc x | [ n∸i≡sx ] =
    let sem = ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ in
      vs (suc i)
    -- ≡⟨ encode-∋ n (forget-last vs) i ⟩
      -- ?
    ≡⟨ {!!} ⟩
      ⟦ encode n (forget-last vs) ⟧ x
    ≡⟨⟩
      sem (suc x)
    -- ≡⟨  Eq.sym (Eq.cong sem (n∸n≡0 n)) ⟩
    --   sem (n ∸ n)
    -- ≡⟨ Eq.cong (λ eq → sem (n ∸ eq)) p ⟩
    --   sem z
    ∎
  -- ... | false because ofⁿ ¬p | x = {!!}
  --   -- let sem = ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧
  --   -- in
  --   --   vs (suc i)
  --   -- ≡⟨ {!!} ⟩
  --   --   sem (n ∸ toℕ i)
  --   -- ∎
  -- ... | true because ofʸ p | zero = {!!}
  -- ... | true because ofʸ p | (suc x) = λ ()
    -- let sem = ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧
    -- in
    --   vs (suc i)
    -- ≡⟨ Eq.cong (λ eq → vs (suc eq)) flipped-p ⟩
    --   vs (suc (fromℕ n))
    -- ≡⟨⟩
    --   sem zero
    -- ≡⟨  Eq.sym (Eq.cong sem (n∸n≡0 n)) ⟩
    --   sem (n ∸ n)
    -- ≡⟨ Eq.cong (λ eq → sem (n ∸ eq)) p ⟩
    --   sem (n ∸ toℕ i)
    -- ∎
    -- where
    --     ss : toℕ i ≡ n
    --     ss = Eq.sym p

    --     flipped-p : i ≡ fromℕ n
        -- flipped-p = toℕ-cong n i (Eq.sym p)
    --   vs (suc i)
    -- ≡⟨ {!!} ⟩ --encode-∋ n (forget-last vs) zero ⟩
    --   -- ⟦ encode n (forget-last vs) ⟧ n
    -- -- ≡⟨⟩
    --   ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (suc n ∸ toℕ (suc i))
    -- ≡⟨⟩
    --   ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (⊇-conf (suc n) (suc i))
    -- ∎

  encode-⊆ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → ⟦ encode n vs ⟧ ⊆ vs
  encode-⊆ n vs c = ⊆-conf n c , encode-∈ n vs c

  encode-⊇ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → vs ⊆ ⟦ encode n vs ⟧
  encode-⊇ n vs i = ⊇-conf n i , encode-∋ n vs i

VariantList-is-complete : Complete VariantListL
VariantList-is-complete {A} {n} vs =
  let open Completeness A
   in (record { get = encode n vs }) , encode-⊇ n vs , encode-⊆ n vs
```



