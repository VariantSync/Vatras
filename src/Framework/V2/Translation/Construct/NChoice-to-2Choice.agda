{-# OPTIONS --sized-types #-}
module Framework.V2.Translation.Construct.NChoice-to-2Choice {Q : Set} where

open import Data.Bool using (Bool; false; true) renaming (_≟_ to _≟ᵇ_)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat using (ℕ; suc; zero; _+_; _≡ᵇ_; _<_; _≤_; s≤s; z≤n) renaming (_≟_ to _≟ⁿ_)
import Data.Nat.Properties as Nat
open import Data.Product using (∃-syntax; Σ; proj₁; proj₂; Σ-syntax) renaming (_,_ to _and_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Level
open import Size using (Size; ↑_; ∞)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet
open import Util.List using (find-or-last)

open import Relation.Binary using (Setoid; IsEquivalence)

open import Util.AuxProofs using (true≢false; n≡ᵇn; n<m→m≡ᵇn)
open import Framework.V2.Definitions using (evalConfig; unrestricted)
open import Framework.V2.Annotation.IndexedName using (IndexedName; _∙_; show-IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂; show to show-2choice)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)

open import Data.String using (String; _++_)

private
  I = IndexedName Q

NConfig = Configₙ Q
2Config = Config₂ I

record ConfContract (D : Q) (Rₙ : (Q → ℕ) → Set) (R₂ : (I → Bool) → Set) (conf : NConfig Rₙ → 2Config R₂) : Set where
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
    select-n : ∀ (c : NConfig Rₙ) {i : ℕ}
      → evalConfig c D ≡ i
      → evalConfig (conf c) (D ∙ i) ≡ true

    {-|
    All alternatives before the desired alternative must be deselected so
    that we go right until we find the correct alternative to pick.
    -}
    deselect-<n : ∀ (c : NConfig Rₙ) {i : ℕ}
      → i < evalConfig c D
      → evalConfig (conf c) (D ∙ i) ≡ false

    {-|
    There is no third requirement because we do not care
    for the values of the translated configuration for dimensions
    deeper than (c D).
    These alternatives will never be reached upon configuration.
    -}
open ConfContract

record FnocContract (D : Q) (R₂ : (I → Bool) → Set) (Rₙ : (Q → ℕ) → Set) (fnoc : 2Config R₂ → NConfig Rₙ) : Set where
  field
    {-|
    The nary config must chose index i if
    - the alternative at nesting depth i is chosen in the binary expression
    - and no other alternative at a higher nesting depth was chosen.
    -}
    correct : ∀ (c : 2Config R₂) (i : ℕ)
      → evalConfig c (D ∙ i) ≡ true
      → (∀ (j : ℕ) → j < i → evalConfig c (D ∙ j) ≡ false)
      → evalConfig (fnoc c) D ≡ i

    {-|
    The nary config must not choose an index i if the alternative at nesting
    depth i in the binary expressio is not chosen
    |-}
    incorrect : ∀ (c : 2Config R₂) (i : ℕ)
      → evalConfig c (D ∙ i) ≡ false
      → evalConfig (fnoc c) D ≢ i
open FnocContract

module Translate {ℓ₂} (S : Setoid Level.zero ℓ₂) where
  open Setoid S
  module ≈-Eq = IsEquivalence isEquivalence

  {-| A dialect of binary choice calculus in which all data is in leaves. -}
  data NestedChoice : Size → Set where
    val  : ∀ {i : Size} → Carrier → NestedChoice i
    nchc : ∀ {i : Size} → 2Choice I (NestedChoice i) → NestedChoice (↑ i)

  ⟦_⟧ : ∀ {i : Size} {R₂ : (I → Bool) → Set} → (NestedChoice i) → 2Config R₂ → Carrier
  ⟦ val  v   ⟧ c = v
  ⟦ nchc chc ⟧ c = ⟦ ⟦ chc ⟧₂ ((λ i → evalConfig c i) and tt) ⟧ c

  show-nested-choice : ∀ {i} → (Q → String) → (Carrier → String) → NestedChoice i → String
  show-nested-choice show-q show-carrier ( val v) = show-carrier v
  show-nested-choice show-q show-carrier (nchc c) =
    show-2choice
      (show-IndexedName show-q)
      (show-nested-choice show-q show-carrier)
      c

  -- TODO?: Replace NestedChoice by 2ADT
  -- open import Framework.V2.Lang.2ADT Q using (2ADT; 2ADTAsset; 2ADTChoice; semantics)
  -- NestedChoice : Size → Set
  -- NestedChoice i = 2ADT i I
  -- val = 2ADTAsset
  -- nchc = 2ADTChoice
  -- ⟦_⟧ : ∀ {i : Size} → (NestedChoice i) → 2Config → Carrier
  -- ⟦_⟧ = semantics ???? -- this should work

  convert' : Q → Carrier → List Carrier → ℕ → NestedChoice ∞
  convert' D l []       n = val l
  convert' D l (r ∷ rs) n = nchc ((D ∙ n) ⟨ val l , convert' D r rs (suc n) ⟩)

  convert : NChoice Q Carrier → NestedChoice ∞
  convert (D ⟨ c ∷ cs ⟩) = convert' D c cs zero

  module Preservation
      {Rₙ : (Q → ℕ) → Set}
      {R₂ : (I → Bool) → Set}
      (conf : NConfig Rₙ → 2Config R₂)
      (fnoc : 2Config R₂ → NConfig Rₙ)
      where
    open Data.IndexedSet S using (_⊆[_]_; _≅[_][_]_; _≅_)

    preserves-conf :
      ∀ (chc : NChoice Q Carrier)
      → ConfContract (NChoice.dim chc) Rₙ R₂ conf
        -----------------------------------
      → ⟦ chc ⟧ₙ ⊆[ conf ] ⟦ convert chc ⟧
    preserves-conf (D ⟨ l ∷ rs ⟩) confContract c
      = induction l rs
                  (evalConfig c D) 0
                  (Nat.+-comm (evalConfig c D) zero)
      where
        {-
        The heart of this induction proof lies in proving that
        `config-without-proof (conf c) (D ∙ m)` has the value we desire. Hereby,
        `m` is the choice index generated by `convert'`. From `ConfContract` we
        get `select-n` and `deselect-<n` but in order to demand these guarantees
        we need to proof either `m < c D` or `m ≡ c D`. As `m` varies in the
        induction we need to relate `m` to `c D` using an invariant. The
        function `convert'` increases `m` each iteration and `c D` is constant.
        Hence, we introduce `n` which decreases each iteration such that we have
        `n + m ≡ c D`.
        -}
        induction : (l : Carrier) → (rs : List Carrier)
                  → (n m : ℕ)
                  → n + m ≡ evalConfig c D
                  → find-or-last n (l ∷ rs) ≈ ⟦ convert' D l rs m ⟧ (conf c)
        -- Only one alternative left
        induction l [] n m n+m≡cD = ≈-Eq.refl
        -- Select the current alternative (numbered `m`) because
        -- `c D = 0 + m = m`
        induction l (r ∷ rs) zero m m≡cD
          rewrite select-n confContract c (Eq.sym m≡cD)
          = ≈-Eq.refl
        -- Ignore the current alternative (numbered `m`) and select one of the
        -- later alternatives (numbered `> m`) because `c D = suc n + m` and
        -- thus `c D > m`
        induction l (r ∷ rs) (suc n) m n+m≡cD
          rewrite Eq.sym (Nat.+-suc n m)
          rewrite deselect-<n confContract c (Nat.m+n≤o⇒n≤o n (Nat.≤-reflexive n+m≡cD))
          = induction r rs n (suc m) n+m≡cD

    preserves-fnoc :
      ∀ (chc : NChoice Q Carrier)
      → FnocContract (NChoice.dim chc) R₂ Rₙ fnoc
        -----------------------------------
      → ⟦ convert chc ⟧ ⊆[ fnoc ] ⟦ chc ⟧ₙ
    preserves-fnoc (D ⟨ l ∷ rs ⟩) fnocContract c
      = induction l rs
                  zero (evalConfig (fnoc c) D)
                  Eq.refl
                  (λ where j ())
      where
        {-
        The idea of this induction is the same as for the preserves-conf. In
        particular, `m` is the index of the current alternative and `n` is used
        to relate `m` to `fnoc c D` with `fnoc c D ≡ n + m`. However, in order
        to  fulfill FnocContract we also need to remember (in `ps`) that all
        alternatives with an index `< n` where not selected.
        -}
        induction : (l : Carrier) → (rs : List Carrier)
                  → (n m : ℕ)
                  → evalConfig (fnoc c) D ≡ n + m
                  → (∀ (j : ℕ) → j < n → evalConfig c (D ∙ j) ≡ false)
                  → ⟦ convert' D l rs n ⟧ c ≈ find-or-last m (l ∷ rs)
        -- Only one alternative left
        induction l [] n m p ps = ≈-Eq.refl
        induction l (r ∷ rs) n m p ps with evalConfig c (D ∙ n) in selected
        -- Select the current alternative because it is the first one where
        -- `config-without-proof c (D ∙ n)` is true
        ... | true
          rewrite correct fnocContract c n selected ps
          rewrite Nat.+-comm n m
          rewrite Eq.sym (Nat.+-cancelʳ-≡ n zero m p)
          = ≈-Eq.refl
        -- Impossible case: `config-without-proof c (D ∙ n)` is `false` hence
        -- `incorrect` guarantees `fnoc c D ≢ n` but we have
        -- `fnoc c D ≡ n + 0 = n`
        induction l (r ∷ rs) n zero p ps | false
          rewrite Nat.+-comm n zero
          = ⊥-elim (incorrect fnocContract c n selected p)
        -- One of the next alternatives needs to be selected because
        -- `config-without-proof c (D ∙ n)` is `false`
        induction l (r ∷ rs) n (suc m) p ps | false
          rewrite Nat.+-suc n m
          = induction r rs (suc n) m p ps'
          where
            ps' : (j : ℕ) → j < suc n → evalConfig c (D ∙ j) ≡ false
            ps' j i<suc-n with j ≟ⁿ n
            ... | no p = ps j (Nat.≤∧≢⇒< (Nat.≤-pred i<suc-n) p)
            ... | yes refl = selected

    convert-preserves :
      ∀ (chc : NChoice Q Carrier)
      → ConfContract (NChoice.dim chc) Rₙ R₂ conf
      → FnocContract (NChoice.dim chc) R₂ Rₙ fnoc
        ------------------------------------------
      → ⟦ chc ⟧ₙ ≅[ conf ][ fnoc ] ⟦ convert chc ⟧
    convert-preserves chc conv vnoc = preserves-conf chc conv and preserves-fnoc chc vnoc

{-|
There needs to be at least one true alternative.
In particular, `default-fnoc'` needs to pattern match on `i` to proof to the
termination checker that it wont search for a non-existing true alternative.
|-}
at-least-true-once : (I → Bool) → Set
at-least-true-once c = ∀ (D : Q) → Σ[ i ∈ ℕ ] (c (D ∙ i) ≡ true)

default-conf : ∀ {R} → NConfig R → 2Config at-least-true-once
default-conf c .proj₁ (D ∙ i) = evalConfig c D ≡ᵇ i
default-conf c .proj₂ D = evalConfig c D and n≡ᵇn (evalConfig c D)

default-fnoc' : (D : Q) → (c : I → Bool) → (n i : ℕ) → c (D ∙ (n + i)) ≡ true → ℕ
default-fnoc' D c n i p with c (D ∙ n) ≟ᵇ true
... | yes cn≡true = n
-- Impossible case because `at-least-true-once` guarantees at least one true
-- alternative here.
default-fnoc' D c n zero p | no cn≢true
  rewrite Nat.+-comm n zero
  = ⊥-elim (cn≢true p)
default-fnoc' D c n (suc i) p | no cn≢true
  rewrite Nat.+-suc n i
  = default-fnoc' D c (suc n) i p

default-fnoc : 2Config at-least-true-once → NConfig unrestricted
default-fnoc (c and p) .proj₁ D with p D
... | i and p' = default-fnoc' D c zero i p'
default-fnoc c .proj₂ = tt

default-conf-satisfies-contract : (D : Q) → (R : (Q → ℕ) → Set) → ConfContract D R at-least-true-once default-conf
default-conf-satisfies-contract D R .select-n c refl
  rewrite n≡ᵇn (evalConfig c D)
  = refl
default-conf-satisfies-contract D R .deselect-<n c i≤cD
  rewrite n<m→m≡ᵇn i≤cD
  = refl

default-fnoc-satisfies-contract : (D : Q) → FnocContract D at-least-true-once unrestricted default-fnoc
default-fnoc-satisfies-contract D .correct (c and p) i' ci'≡true c<i'≡false with p D
... | i and p' = induction zero i p' i' refl
  where
    {-
    Similar to the inductions used for proving `preserves-conf`, this induction
    introcudes a new number `m` to relate `n` to `i'`. Hence, we a lot of
    different numbers. In particular:
      - `n` is the current alternative index which `default-fnoc'` probes. It is
        increased each iteration and all alternatives below this number where
        deselected by the config `c`.
      - `i` is the index where it is guaranteed that the config `c` is `true`
        (only needed for proving termination of `default-fnoc'`).
      - `i'` is the index where the config `c` should be `true` the first time.
        (To be proven by this induction.) The `FnocContract` guarantees that `c`
        is `false for indices `< i'` and true for `i'`.
      - `m` is a helper for relating `n` to `i'` with `n + m ≡ i'`. This allows
        us to proof the prerequesites for the `FnocContract`.
    -}
    induction : (n i : ℕ) → (p : c (D ∙ (n + i)) ≡ true) → (m : ℕ) → (n + m ≡ i') → default-fnoc' D c n i p ≡ i'
    induction n i p m m+n≡i' with c (D ∙ n) ≟ᵇ true
    -- We found the alternative index because `c (D ∙ n)` is true for the first
    -- time.
    induction n i p zero m+n≡i' | yes cn≡true
      rewrite Nat.+-comm n zero
      = m+n≡i'
    -- Impossible case because `c (D ∙ n)` is true but we have `n + suc m = i'`,
    -- thus `n < i'` and `FnocContract` guarantees that `c (D ∙ n)` is false.
    induction n i p (suc m) m+n≡i' | yes cn≡true
      rewrite Nat.+-suc n m
      = ⊥-elim (true≢false cn≡true (c<i'≡false n (Nat.m+n≤o⇒m≤o (suc n) (Nat.≤-reflexive m+n≡i'))))
    -- Impossible case because `c (D ∙ n)` is false but, for termination
    -- checking, this case is guaranteed to have a true config.
    induction n zero p m m+n≡i' | no cn≢true
      rewrite Nat.+-comm n zero
      = ⊥-elim (cn≢true p)
    -- Impossible case because `c (D ∙ n)` is false and we have
    -- `i' = n + zero = n` and hence `FnocContract` guarantees that `c (D ∙ n)`
    -- is true.
    induction n (suc i) p zero m+n≡i' | no cn≢true
      rewrite Nat.+-comm n zero
      rewrite m+n≡i'
      = ⊥-elim (cn≢true ci'≡true)
    -- Try next index because `c (D ∙ n)` is still false.
    induction n (suc i) p (suc m) m+n≡i' | no cn≢true
      rewrite Nat.+-suc n i
      rewrite Nat.+-suc n m
      = induction (suc n) i p m m+n≡i'
default-fnoc-satisfies-contract D .incorrect (c and p) i' ci'≡false with p D
... | i and p' = induction zero i p'
  where
    induction : (n i : ℕ) → (p : c (D ∙ (n + i)) ≡ true) → default-fnoc' D c n i p ≢ i'
    induction n i p n≡i' with c (D ∙ n) ≟ᵇ true
    -- We found the alternative index because `c (D ∙ n)` is true for the first
    -- time.induction n i p n≡i' | yes cn≡true
    induction n i p n≡i' | yes cn≡true
      rewrite Eq.sym n≡i'
      = true≢false cn≡true ci'≡false
    -- Impossible because `c (D ∙ n)` is false and we assume `n = i'` and hence
    -- `FnocContract` guarantees that `c (D ∙ n)` is true.
    induction n zero p n≡i' | no cn≢true
      rewrite Nat.+-comm n zero
      = cn≢true p
    -- Try next index because `c (D ∙ n)` is still false.
    induction n (suc i) p n≡i' | no cn≢true
      rewrite Nat.+-suc n i
      = induction (suc n) i p n≡i'
