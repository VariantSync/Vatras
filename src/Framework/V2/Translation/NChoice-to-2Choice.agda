module Framework.V2.Translation.NChoice-to-2Choice where

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

import Data.IndexedSet
open import Util.List using (find-or-last)

open import Framework.V2.Definitions
open import Framework.V2.Variants using (VariantSetoid)
open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩)
open Chc.Choiceₙ using (_⟨_⟩)

private
  variable
    A : 𝔸

  BinaryChoice = VLChoice₂.Syntax
  BinaryChoice-Semantics = VLChoice₂.Semantics
  Choice = VLChoiceₙ.Syntax
  Choice-Semantics = VLChoiceₙ.Semantics

record IndexedDimension (F : 𝔽) : Set where
  constructor _∙_
  field
    dim : F
    index : ℕ

module N→2-Choice
  {V F}
  (VL₁ : VariabilityLanguage V F ℕ)
  (VL₂ : VariabilityLanguage V (IndexedDimension F) Bool)
  (L₂-has-choices : VLChoice₂.Construct V (IndexedDimension F) ⟦∈⟧ VL₂)
  (t : expression-set VL₁ A → expression-set VL₂ A)
  where
  open Data.Nat using (_∸_; _≤_)
  open import Data.Nat.Show using (show)

  private
    I = IndexedDimension F
    NConfig = Config F ℕ
    2Config = Config I Bool
    L₁   = expression-set VL₁
    L₂   = expression-set VL₂
    ⟦_⟧₁ = semantics VL₁ {A}
    ⟦_⟧₂ = semantics VL₂ {A}

    L₂-has-choices-syntactically : BinaryChoice I ∈ₛ L₂
    L₂-has-choices-syntactically = make L₂-has-choices

    mkChoice : BinaryChoice I L₂ A → L₂ A
    mkChoice = cons L₂-has-choices-syntactically

    mkChoice-preserves : ∀ (c : BinaryChoice I L₂ A) → ⟦ mkChoice c ⟧₂ ≗ BinaryChoice-Semantics VL₂ c
    mkChoice-preserves = preservation L₂-has-choices


  open import Data.Vec using (Vec; []; _∷_; fromList)

  unroll : ∀ {n}
    → (max : ℕ)
    → F      -- initial dimension in input formula that we translate (D in the example above).
    → Vec (L₁ A) (suc n) -- remaining alternatives of the choice to unroll. We let this shrink recursively.
    → BinaryChoice I L₂ A
  unroll {n} max D (e ∷ [])     = (D ∙ (max ∸ n)) ⟨ t e , t e ⟩
  unroll {n} max D (l ∷ r ∷ es) = (D ∙ (max ∸ n)) ⟨ t l , mkChoice (unroll max D (r ∷ es)) ⟩
  -- an unrolled choice D ∙ i gives you i effective choices

  convert : Choice F L₁ A → BinaryChoice I L₂ A
  convert (D ⟨ e ∷ es ⟩) = unroll #es D (e ∷ fromList es)
    where #es = Data.List.length es

  -- unroll-name : ∀ (D : F) (e : L₁ A) (es : List (L₁ A)) (n : ℕ)
    -- → Σ[ x ∈ L₂ A ] (unroll D (e ∷ es) n ≡ (D ∙ n) ⟨ t e , x ⟩)
  -- unroll-name D e [] n = t e and refl
  -- unroll-name D e (r ∷ rs) n = mkChoice (unroll D (r ∷ rs) (suc n)) and refl

  open Data.Nat using (_<_; _≤_; s≤s; z≤n)
  record ConfSpec (D : F) (conf : NConfig → 2Config) : Set where
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
        → i ≡ c D
        → (conf c) (D ∙ i) ≡ true

      {-|
      All alternatives before the desired alternative must be deselected so
      that we go right until we find the correct alternative to pick.
      -}
      deselect-<n : ∀ (c : NConfig) {i : ℕ}
        → i < c D
        → (conf c) (D ∙ i) ≡ false

      {-|
      There is no third requirement because we do not care
      for the values of the translated configuration for dimensions
      deeper than (c D).
      These alternatives will never be reached upon configuration.
      -}
  open ConfSpec

  record FnocSpec (n : ℕ) (fnoc : 2Config → NConfig) : Set where
    field
      {-|
      The nary config must chose index i iff
      - the alternative at nesting depth i is chosen in the binary expression
      - and no other alternative at a higher nesting depth was chosen.
      -}
      correct : ∀ (c : 2Config) (D : F) (i : ℕ)
        → c (D ∙ i) ≡ true
        → (∀ (j : ℕ) → j < i → c (D ∙ j) ≡ false)
        → (fnoc c) D ≡ i
  open FnocSpec

  module Preservation
    (D : F)
    (confi : NConfig → 2Config)
    (fnoci : 2Config → NConfig)
    where
    open Data.List using (length)
    open import Data.List.Relation.Unary.All using (All; []; _∷_)
    open import Data.List.NonEmpty.Relation.Unary.All using (_∷_) renaming (All to All⁺)
    open Data.IndexedSet (VariantSetoid V A) using () renaming (_≅_ to _≋_)
    open import Util.AuxProofs using (if-idemp)
    open Eq.≡-Reasoning
    open Data.Nat using (_+_)
    open import Data.Nat.Properties using (≤-refl; m∸n≤m; m∸n≢0⇒n<m; 0∸n≡0; n∸n≡0; m≤n⇒m∸n≡0)

    -- convert-preserves-l : ∀ (e : L₁ A) (es : List (L₁ A)) (c : NConfig)
    --   → ConfSpec D confi
    --   -- → ConfSpec D (length es) confi
    --   → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) (e ∷ es)
    --   →   Choice-Semantics       VL₁ (D ⟨ e ∷ es ⟩) c
    --     ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ es ⟩)) (confi c)
    convert-preserves-l : ∀ (e : L₁ A) (es : List (L₁ A)) (c : NConfig)
      → ConfSpec D confi
      → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) (e ∷ es)
      → (max : ℕ)
      → (i : ℕ)
      -- → i + length es ≡ max
      → length es ≤ max
      → max ≤ i + length es
      -- → max ∸ length es ≤ i
      → c D ≡ i
      →   ⟦ find-or-last (i ∸ (max ∸ length es)) (e ∷ es) ⟧₁ c
        ≡ BinaryChoice-Semantics VL₂ (unroll max D (e ∷ fromList es)) (confi c)
        -- ≡ BinaryChoice-Semantics VL₂ (unroll (length es) D (e ∷ fromList es)) (confi c)

    convert-preserves-l-base : ∀ (e : L₁ A) (c : NConfig)
      → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)
      →   Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
        ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ [] ⟩)) (confi c)
    convert-preserves-l-base e c e≡te =
      begin
        Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
      ≡⟨⟩
        ⟦ e ⟧₁ c
      ≡⟨ e≡te ⟩
        ⟦ t e ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ eq → ⟦ eq ⟧₂ (confi c))
           (Eq.sym
             (if-idemp ((confi c) (D ∙ 0)))) ⟩
        ⟦ if ((confi c) (D ∙ 0)) then (t e) else (t e) ⟧₂ (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ [] ⟩)) (confi c)
      ∎

    convert-preserves-l-base' : ∀ (e : L₁ A) (c : NConfig)
      → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)
      → (max : ℕ)
      →   Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
        ≡ BinaryChoice-Semantics VL₂ (unroll max D (e ∷ [])) (confi c)
    convert-preserves-l-base' e c e≡te max =
      begin
        Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
      ≡⟨⟩
        ⟦ e ⟧₁ c
      ≡⟨ e≡te ⟩
        ⟦ t e ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ eq → ⟦ eq ⟧₂ (confi c))
           (Eq.sym
             (if-idemp ((confi c) (D ∙ max)))) ⟩
        ⟦ if ((confi c) (D ∙ max)) then (t e) else (t e) ⟧₂ (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ (unroll max D (e ∷ [])) (confi c)
      ∎

    convert-preserves-l-step : ∀ (l r : L₁ A) (es : List (L₁ A)) (c : NConfig)
       → (conv : ConfSpec D confi)
       -- → ConfSpec D (suc (length es)) confi
       → (hypot : All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) (l ∷ r ∷ es))
       → (max : ℕ)
       -- → length (r ∷ es) ≤ max
       → (i : ℕ)
       -- → max ≤ i + length (r ∷ es)
       → (n≤max : length (r ∷ es) ≤ max)
       → (max≤i+n : max ≤ i + length (r ∷ es))
       → (cD≡i : c D ≡ i)
       -- →   Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
       →   ⟦ find-or-last (i ∸ (max ∸ length (r ∷ es))) (l ∷ r ∷ es) ⟧₁ c
         -- ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
         ≡ BinaryChoice-Semantics VL₂ (unroll max D (l ∷ fromList (r ∷ es))) (confi c)
    convert-preserves-l-step l r es c conv (l≡tl ∷ _) (suc max) zero (s≤s n≤max) (s≤s max≤i+n) cD≡i =
      begin
        ⟦ find-or-last (zero ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
      ≡⟨ Eq.cong
           (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
           (0∸n≡0 (max ∸ n)) ⟩
        ⟦ l ⟧₁ c
      ≡⟨ l≡tl ⟩
        ⟦ t l ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ x → ⟦ if x then t l else tail ⟧₂ (confi c))
           (Eq.sym (select-n conv c max∸n≡cD)) ⟩
        ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else tail ⟧₂ (confi c)
      ∎
      where n = length es
            tail = mkChoice (unroll (suc max) D (r ∷ fromList es))

            max∸n≡0 : max ∸ n ≡ 0
            max∸n≡0 = m≤n⇒m∸n≡0 max≤i+n

            max∸n≡cD : max ∸ n ≡ c D
            max∸n≡cD = Eq.trans max∸n≡0 (Eq.sym cD≡i)
    convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ es≡tes) (suc max) (suc i) (s≤s n≤max) (s≤s max≤i+n) cD≡i with max ∸ (length es) in eq
    ... | zero =
      begin
        ⟦ find-or-last i (r ∷ es) ⟧₁ c
      ≡⟨ Eq.cong
           (λ x → ⟦ find-or-last x (r ∷ es) ⟧₁ c)
           lh ⟩
        -- ⟦ find-or-last (i ∸ (max ∸ length es)) (r ∷ es) ⟧₁ c
        ⟦ find-or-last (suc i ∸ (suc max ∸ n)) (r ∷ es) ⟧₁ c
      -- ≡⟨ {!!} ⟩
      ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ es≡tes) (suc max) (suc i) n≤1+m 1+m≤1+i+n cD≡i ⟩
      -- ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ es≡tes) (suc max) (suc i) ? cD≡i ⟩
        BinaryChoice-Semantics VL₂ (unroll (suc max) D (r ∷ fromList es)) (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ tail (confi c)
      ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
        ⟦ mkChoice tail ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
           (Eq.sym (deselect-<n conv c 0<cD)) ⟩
        ⟦ if (confi c) (D ∙ zero) then t l else mkChoice tail ⟧₂ (confi c)
      ∎
      where tail = unroll (suc max) D (r ∷ fromList es)
            n    = length es

            0<cD : zero < c D
            0<cD rewrite cD≡i = s≤s z≤n

            max∸n≡0 : max ∸ n ≡ 0
            max∸n≡0 = eq

            m≤n : max ≤ n
            m≤n = {!!} -- follows from max∸n≡0

            m≡n : max ≡ n
            m≡n = {!!} -- from m≤n and n≤max

            [1+m]∸n≡1 : suc max ∸ n ≡ 1
            [1+m]∸n≡1 rewrite m≡n = {!!} -- follows from 1 + x - x = x

            lh : i ≡ suc i ∸ (suc max ∸ n)
            lh rewrite [1+m]∸n≡1 = refl

            n≤1+m : n ≤ suc max
            n≤1+m rewrite m≡n = {!!} -- follows from x ≤ 1 + x

            1+m≤1+i+n : suc max ≤ suc (i + n)
            1+m≤1+i+n rewrite m≡n = s≤s {!!} -- follows from x ≤ y + x
    ... | suc d = -- maybe split on i here?
      begin
        ⟦ find-or-last (i ∸ d) (l ∷ r ∷ es) ⟧₁ c
      ≡⟨ {!!} ⟩
        ⟦ if (confi c) (D ∙ suc d) then t l else mkChoice tail ⟧₂ (confi c)
      ∎
      where tail = unroll (suc max) D (r ∷ fromList es)
            n    = length es

            m∸n≡1+d : max ∸ n ≡ suc d
            m∸n≡1+d = eq

            n<m : n < max
            n<m = {!!} -- follows from m∸n≡1+d

            m∸n≤i : max ∸ n ≤ i
            m∸n≤i = {!!} -- I think, we cannot prove this.

            0<m∸n : 0 < max ∸ n
            0<m∸n = {!!} -- follows from m∸n≡1+d

            1+d<cD : suc d < c D
            1+d<cD rewrite cD≡i | Eq.sym m∸n≡1+d = s≤s m∸n≤i
      -- begin
      --   -- Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
      -- -- ≡⟨⟩
      --   -- ⟦ find-or-last (c D) (l ∷ r ∷ es) ⟧₁ c
      -- -- ≡⟨ Eq.cong
      --      -- (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
      --      -- cD≡i ⟩
      --   ⟦ find-or-last (suc i ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
      -- -- ≡⟨⟩
      --   -- ⟦ find-or-last i (r ∷ es) ⟧₁ c
      -- ≡⟨ {!!} ⟩ -- {!convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max ? (suc i) cD≡i!} ⟩
      -- --   BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
      -- -- ≡⟨⟩
      -- --   BinaryChoice-Semantics VL₂ tail (confi c)
      -- -- ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
      --   ⟦ mkChoice tail ⟧₂ (confi c)
      -- ≡⟨ Eq.cong
      --      (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
      --      (Eq.sym (deselect-<n conv c {!!})) ⟩
      --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else mkChoice tail ⟧₂ (confi c)
      -- ∎
      -- where n = length es
      --       tail = unroll (suc max) D (r ∷ fromList es)
      -- begin
      --   ⟦ find-or-last (zero ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
      -- ≡⟨ Eq.cong
      --      (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
      --      (0∸n≡0 (max ∸ n)) ⟩
      --   ⟦ l ⟧₁ c
      -- ≡⟨ l≡tl ⟩
      --   ⟦ t l ⟧₂ (confi c)
      -- ≡⟨ Eq.cong
      --      (λ x → ⟦ if x then t l else tail ⟧₂ (confi c))
      --      (Eq.sym (select-n conv c max∸n≡cD)) ⟩
      --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else tail ⟧₂ (confi c)
      -- ∎
      -- where n = suc (length es)
      --       tail = mkChoice (unroll max D (r ∷ fromList es))

      --       max∸n≡0 : max ∸ n ≡ 0
      --       max∸n≡0 = m≤n⇒m∸n≡0 max≤n

      --       max∸n≡cD : max ∸ n ≡ c D
      --       max∸n≡cD = Eq.trans max∸n≡0 (Eq.sym cD≡i)
      --       -- pick : suc n ∸ c D ≡ suc n
      --       -- pick rewrite cD≡i = refl
    -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ es≡tes) zero (suc i) n≤max z≤n cD≡i =
    --   begin
    --     ⟦ find-or-last i (r ∷ es) ⟧₁ c
    --   ≡⟨ {!!} ⟩
    --   -- ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max (suc i) asd cD≡i ⟩
    --     BinaryChoice-Semantics VL₂ (unroll zero D (r ∷ fromList es)) (confi c)
    --   ≡⟨⟩
    --     BinaryChoice-Semantics VL₂ tail (confi c)
    --   ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    --     ⟦ mkChoice tail ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    --        (Eq.sym (deselect-<n conv c {! doable!})) ⟩
    --     ⟦ if (confi c) (D ∙ zero) then t l else mkChoice tail ⟧₂ (confi c)
    --   ∎
    --   where tail = unroll zero D (r ∷ fromList es)
    -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ es≡tes) (suc max) (suc i) max∸n≤i cD≡i = {!!}
    -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ hypot-es) max (suc i) max≤1+i+n cD≡i with max ∸ length (r ∷ es) in eq
    -- ... | zero =
    --   begin
    --     ⟦ find-or-last i (r ∷ es) ⟧₁ c
    --   ≡⟨ {!!} ⟩
    --     ⟦ find-or-last (suc i ∸ (max ∸ length es)) (r ∷ es) ⟧₁ c
    --   ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max (suc i) asd cD≡i ⟩
    --     BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
    --   ≡⟨⟩
    --     BinaryChoice-Semantics VL₂ tail (confi c)
    --   ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    --     ⟦ mkChoice tail ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    --        (Eq.sym (deselect-<n conv c {! doable!})) ⟩
    --     ⟦ if (confi c) (D ∙ zero) then t l else mkChoice tail ⟧₂ (confi c)
    --   ∎
    --   where tail = unroll max D (r ∷ fromList es)
    --         asd : max ∸ length es ≤ suc i
    --         asd = {!!}

    -- ... | suc x = {!!}
      -- begin
      --   -- Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
      -- -- ≡⟨⟩
      --   -- ⟦ find-or-last (c D) (l ∷ r ∷ es) ⟧₁ c
      -- -- ≡⟨ Eq.cong
      --      -- (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
      --      -- cD≡i ⟩
      --   ⟦ find-or-last ((suc i) ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
      -- -- ≡⟨⟩
      --   -- ⟦ find-or-last i (r ∷ es) ⟧₁ c
      -- ≡⟨ {!!} ⟩ -- {!convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max ? (suc i) cD≡i!} ⟩
      --   BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
      -- ≡⟨⟩
      --   BinaryChoice-Semantics VL₂ tail (confi c)
      -- ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
      --   ⟦ mkChoice tail ⟧₂ (confi c)
      -- ≡⟨ Eq.cong
      --      (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
      --      (Eq.sym (deselect-<n conv c {!!})) ⟩
      --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else mkChoice tail ⟧₂ (confi c)
      -- ∎
      -- where n = length (r ∷ es)
      --       tail = unroll max D (r ∷ fromList es)

      --       -- TODO: Move to aux proofs
      --       asdf : ∀ {n m} → suc (n ∸ m) ≤ suc n
      --       asdf {zero} {zero} = s≤s z≤n
      --       asdf {zero} {suc _} = s≤s z≤n
      --       asdf {suc n} {zero} = ≤-refl
      --       asdf {suc n} {suc m} = s≤s (m∸n≤m (suc n) (suc m))

            -- pick : max ∸ n < c D
            -- pick rewrite cD≡i = s≤s {!!}

    convert-preserves-l e [] c _ (e≡te ∷ []) max _ _ _ _ = convert-preserves-l-base' e c e≡te max
    convert-preserves-l l (r ∷ es) c conv hypot max i asd eq cD≡i = convert-preserves-l-step l r es c conv hypot max i asd eq cD≡i

    -- convert-preserves-l :
    --     ConfSpec D confi
    --   → (alts : List⁺ (L₁ A))
    --   → (c : NConfig)
    --   → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) alts
    --   →   Choice-Semantics       VL₁ (D ⟨ alts ⟩) c
    --     ≡ BinaryChoice-Semantics VL₂ (unroll D alts zero) (confi c)
    -- convert-preserves-l conv (e ∷ []) c (e≡tx ∷ []) =
    --   begin
    --     Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
    --   ≡⟨⟩
    --     ⟦ e ⟧₁ c
    --   ≡⟨ e≡tx ⟩
    --     ⟦ t e ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ eq → ⟦ eq ⟧₂ (confi c))
    --        (Eq.sym
    --          (if-idemp ((confi c) (D ∙ 0)))) ⟩
    --     ⟦ if ((confi c) (D ∙ 0)) then (t e) else (t e) ⟧₂ (confi c)
    --   ≡⟨⟩
    --     BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ [] ⟩)) (confi c)
    --   ∎
    -- convert-preserves-l conv (l ∷ r ∷ es) c (l≡tl ∷ r≡tr ∷ hypot-es) with c D in eq
    -- ... | zero  =
    --   begin
    --     ⟦ l ⟧₁ c
    --   ≡⟨ l≡tl ⟩
    --     ⟦ t l ⟧₂ (confi c)
    --   ≡⟨⟩
    --     ⟦ if true then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ x → ⟦ if x then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c))
    --        (Eq.sym (select-n conv c 0 (Eq.sym eq))) ⟩
    --     ⟦ if (confi c) (D ∙ 0) then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    --   ≡⟨⟩
    --     BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
    --   ∎
    -- ... | suc n =
    --   begin
    --     ⟦ find-or-last n (r ∷ es) ⟧₁ c
    --   -- ≡⟨ {!!} ⟩
    --     -- ⟦ ⟧₂
    --   -- ≡⟨⟩
    --     -- BinaryChoice-Semantics VL₂ (unroll D (r ∷ es) zero) (confi c)
    --   ≡⟨ {!!} ⟩
    --     BinaryChoice-Semantics VL₂ (unroll D (r ∷ es) 1) (confi c)
    --   ≡⟨ Eq.sym (mkChoice-preserves (unroll D (r ∷ es) 1) (confi c)) ⟩
    --     ⟦ mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    --   ≡⟨⟩
    --     ⟦ if false then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ x → ⟦ if x then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c))
    --        (Eq.sym (deselect-<n conv c 0 {!!})) ⟩
    --     ⟦ if (confi c) (D ∙ 0) then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    --   ≡⟨⟩
    --     BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
    --   ∎

    convert-preserves : ∀ (alts : List⁺ (L₁ A)) →
          Choice-Semantics       VL₁ (D ⟨ alts ⟩)
        ≋ BinaryChoice-Semantics VL₂ (convert (D ⟨ alts ⟩))
    convert-preserves = {!!}
