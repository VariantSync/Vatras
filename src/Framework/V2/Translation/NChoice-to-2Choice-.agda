{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}
module Framework.V2.Translation.NChoice-to-2Choice- {ℓ₁} {Q : Set ℓ₁} where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat using (ℕ; suc; zero; _+_; _≟_; _≡ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Show renaming (show to show-ℕ)
import Data.Nat.Properties as Nat
open import Data.Product using (∃-syntax; Σ; proj₁; proj₂; Σ-syntax) renaming (_,_ to _and_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (yes; no)

open import Size using (Size; ↑_; ∞)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet
open import Util.List using (find-or-last)

open import Relation.Binary using (Setoid; IsEquivalence)

import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)

open import Data.String using (String; _++_)

record IndexedDimension {ℓ} (Q : Set ℓ) : Set ℓ where
  constructor _∙_
  field
    dim : Q
    index : ℕ

show-indexed-dimension : (Q → String) → IndexedDimension Q → String
show-indexed-dimension show-q (D ∙ i) = show-q D ++ "∙" ++ show-ℕ i

private
  I = IndexedDimension Q
  NConfig = Configₙ Q
  -- 2Config = Config₂ I
  at-least-true-once : Config₂ I → Set ℓ₁
  at-least-true-once c = (d : Q) → Σ[ i ∈ ℕ ] (c (d ∙ i) ≡ true)
  2Config = Σ (Config₂ I) at-least-true-once
  config-without-proof : 2Config → Config₂ I
  config-without-proof = proj₁

record ConfContract (D : Q) (conf : NConfig → 2Config) : Set ℓ₁ where
  field
    {-|
    A translated, binary configuration (conf c)
    has to pick the same alternative as the original configuration c.
    This alternative is nested in the binary term.
    The nesting depth is exactly equal to the alternative index:
    - the first alternative (0) is the left alternative of the root choice at level 0
    - the second alternative (1) is the left alternative of the choice (1) in the right alternative of the root choice 0
    - and so on.
    Hence the translated, binary configuration (conf c)
    has to pick the left alternative (true)
    in the choice at nesting level (c D).
    -}
    select-n : ∀ (c : NConfig) {i : ℕ}
      → c D ≡ i
      → config-without-proof (conf c) (D ∙ i) ≡ true

    {-|
    All alternatives before the desired alternative must be deselected so
    that we go right until we find the correct alternative to pick.
    -}
    deselect-<n : ∀ (c : NConfig) {i : ℕ}
      → i < c D
      → config-without-proof (conf c) (D ∙ i) ≡ false

    {-|
    There is no third requirement because we do not care
    for the values of the translated configuration for dimensions
    deeper than (c D).
    These alternatives will never be reached upon configuration.
    -}
open ConfContract

record FnocContract (D : Q) (fnoc : 2Config → NConfig) : Set ℓ₁ where
  field
    {-|
    The nary config must chose index i iff
    - the alternative at nesting depth i is chosen in the binary expression
    - and no other alternative at a higher nesting depth was chosen.
    -}
    correct : ∀ (c : 2Config) (i : ℕ)
      → config-without-proof c (D ∙ i) ≡ true
      → (∀ (j : ℕ) → j < i → config-without-proof c (D ∙ j) ≡ false)
      → (fnoc c) D ≡ i

    incorrect : ∀ (c : 2Config) (i : ℕ)
      → config-without-proof c (D ∙ i) ≡ false
      → fnoc c D ≢ i
open FnocContract

suc-n+m≡k→m<k : (n m : ℕ) → {k : ℕ} → suc n + m ≡ k → m < k
suc-n+m≡k→m<k n zero refl = s≤s z≤n
suc-n+m≡k→m<k n (suc m) refl = s≤s (suc-n+m≡k→m<k n m (Eq.sym (Nat.+-suc n m)))

n≢n+suc-m : (n m : ℕ) → n ≢ n + suc m
n≢n+suc-m (suc n) m n≡n+m = n≢n+suc-m n m (Nat.suc-injective n≡n+m)

n≡n+m→m≡zero : (n m : ℕ) → n ≡ n + m → m ≡ zero
n≡n+m→m≡zero n zero n≡n+m = refl
n≡n+m→m≡zero n (suc m) n≡n+m = ⊥-elim (n≢n+suc-m n m n≡n+m)

n≡ᵇn : (n : ℕ) → (n ≡ᵇ n) ≡ true
n≡ᵇn zero = refl
n≡ᵇn (suc n) = n≡ᵇn n

n<m→m≡ᵇn : {n m : ℕ} → n < m → (m ≡ᵇ n) ≡ false
n<m→m≡ᵇn {zero} (s≤s n<m) = refl
n<m→m≡ᵇn {suc n} (s≤s n<m) = n<m→m≡ᵇn n<m

module Translate {ℓ₂} (S : Setoid ℓ₁ ℓ₂) where
  open Setoid S
  module ≈-Eq = IsEquivalence isEquivalence

  {-| A dialect of binary choice calculus in which all data is in leaves. -}
  data NestedChoice : Size → Set ℓ₁ where
    val : {i : Size} → Carrier → NestedChoice i
    nchc : {i : Size} → 2Choice Q (NestedChoice i) → NestedChoice (↑ i)

  ⟦_⟧' : {i : Size} → (NestedChoice i) → 2Config → ℕ → Carrier
  ⟦ val n ⟧' c i = n
  ⟦ nchc chc ⟧' c i = ⟦ ⟦ chc ⟧₂ (λ q → config-without-proof c (q ∙ i)) ⟧' c (suc i)

  ⟦_⟧ : {i : Size} → NestedChoice i → 2Config → Carrier
  ⟦ nc ⟧ c = ⟦ nc ⟧' c zero

  convert' : Q → Carrier → List Carrier → NestedChoice ∞
  convert' D l [] = val l
  convert' D l (r ∷ rs) = nchc (D ⟨ val l , (convert' D r rs) ⟩)

  convert : NChoice Q Carrier → NestedChoice ∞
  convert (D ⟨ c ∷ cs ⟩) = convert' D c cs

  module Preservation
      (conf : NConfig → 2Config)
      (fnoc : 2Config → NConfig)
      where
    open Data.IndexedSet S using (_⊆[_]_; _≅[_][_]_; _≅_)

    preserves-conf :
        (chc : NChoice Q Carrier)
      → ConfContract (NChoice.dim chc) conf
      → ⟦ chc ⟧ₙ ⊆[ conf ] ⟦ convert chc ⟧
    preserves-conf (D ⟨ l ∷ rs ⟩) confContract c
      = induction l rs
                  (c D) 0
                  (Nat.+-comm (c D) zero)
      where
        induction : (l : Carrier) → (rs : List Carrier)
                  → (n m : ℕ)
                  → n + m ≡ c D
                  → find-or-last n (l ∷ rs) ≈ ⟦ convert' D l rs ⟧' (conf c) m
        induction l [] n m n+m≡cD = ≈-Eq.refl
        induction l (r ∷ rs) zero m m≡cD
          rewrite select-n confContract c (Eq.sym m≡cD)
          = ≈-Eq.refl
        induction l (r ∷ rs) (suc n) m n+m≡cD
          rewrite deselect-<n confContract c (suc-n+m≡k→m<k _ m n+m≡cD)
          rewrite Eq.sym (Nat.+-suc n m)
          = induction r rs n (suc m) n+m≡cD

    preserves-fnoc :
        (chc : NChoice Q Carrier)
      → FnocContract (NChoice.dim chc) fnoc
      → ⟦ convert chc ⟧ ⊆[ fnoc ] ⟦ chc ⟧ₙ
    preserves-fnoc (D ⟨ l ∷ rs ⟩) fnocContract c
      = induction l rs
                  zero (fnoc c D)
                  Eq.refl
                  (λ where j ())
      where
        induction : (l : Carrier) → (rs : List Carrier)
                  → (n m : ℕ)
                  → fnoc c D ≡ n + m
                  → (∀ (j : ℕ) → j < n → config-without-proof c (D ∙ j) ≡ false)
                  → ⟦ convert' D l rs ⟧' c n ≈ find-or-last m (l ∷ rs)
        induction l [] n m p ps = ≈-Eq.refl
        induction l (r ∷ rs) n m p ps with config-without-proof c (D ∙ n) in selected
        ... | true
          rewrite correct fnocContract c n selected ps
          rewrite n≡n+m→m≡zero n m p
          = ≈-Eq.refl
        induction l (r ∷ rs) n zero p ps | false
          rewrite Nat.+-comm n zero
          = ⊥-elim (incorrect fnocContract c n selected p)
        induction l (r ∷ rs) n (suc m) p ps | false
          rewrite Nat.+-suc n m
          = induction r rs (suc n) m p ps'
          where
            ps' : (j : ℕ) → j < suc n → config-without-proof c (D ∙ j) ≡ false
            ps' j i<suc-n with j ≟ n
            ... | no p = ps j (Nat.≤∧≢⇒< (Nat.≤-pred i<suc-n) p)
            ... | yes refl = selected

    convert-preserves :
        (chc : NChoice Q Carrier)
      → ConfContract (NChoice.dim chc) conf
      → FnocContract (NChoice.dim chc) fnoc
      → ⟦ chc ⟧ₙ ≅[ conf ][ fnoc ] ⟦ convert chc ⟧
    convert-preserves chc conv vnoc = preserves-conf chc conv and preserves-fnoc chc vnoc

conf : NConfig → 2Config
conf c .proj₁ (dim ∙ index) = c dim ≡ᵇ index
conf c .proj₂ dim = c dim and n≡ᵇn (c dim)

true≢false : true ≢ false
true≢false ()

n+0≡n : (n : ℕ) → n + 0 ≡ n
n+0≡n zero = refl
n+0≡n (suc n) rewrite n+0≡n n = refl

fnoc' : (c : ℕ → Bool) → (n i : ℕ) → c (n + i) ≡ true → ℕ
fnoc' c n i p with c n in eq
... | true = n
fnoc' c n zero p | false rewrite n+0≡n n rewrite p = ⊥-elim (true≢false eq)
fnoc' c n (suc i) p | false rewrite Nat.+-suc n i = fnoc' c (suc n) i p

fnoc : 2Config → NConfig
fnoc (c and p) d with p d
... | i and p' = fnoc' (λ i → c (d ∙ i)) zero i p'

confContract : (D : Q) → ConfContract D conf
confContract D .select-n c refl rewrite n≡ᵇn (c D) = refl
confContract D .deselect-<n c i≤cD rewrite n<m→m≡ᵇn i≤cD = refl

fnocContract : (D : Q) → FnocContract D fnoc
fnocContract D .correct (c and p) i' ci'≡true c<i'≡false with p D
... | i and p' = {!!}
fnocContract D .incorrect (c and p) i ci≡false fnoc-dD≡i with p D
... | i and p' = {!!}
