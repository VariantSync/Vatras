{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}
module Framework.V2.Translation.NChoice-to-2Choice {ℓ₁} {Q : Set ℓ₁} where

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List using (List; _∷_; []; map; length)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_)
open import Data.Nat.Show renaming (show to show-ℕ)
open import Data.Product using (∃-syntax; proj₁; proj₂) renaming (_,_ to _and_)

open import Size using (Size; ↑_; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

import Data.IndexedSet
open import Util.List using (find-or-last)

open import Relation.Binary using (Setoid; IsEquivalence)

open import Framework.V2.Definitions using (𝔽)
open import Framework.V2.Compiler using (ConstructCompiler)
open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂; show to show-2choice)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)
open Chc.VLChoice₂ using () renaming (Construct to C₂)
open Chc.VLChoiceₙ using () renaming (Construct to Cₙ)

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
  2Config = Config₂ I

open Data.Nat using (_<_; _≤_; s≤s; z≤n)
record ConfSpec (D : Q) (conf : NConfig → 2Config) : Set ℓ₁ where
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

record FnocSpec (D : Q) (fnoc : 2Config → NConfig) : Set ℓ₁ where
  field
    {-|
    The nary config must chose index i iff
    - the alternative at nesting depth i is chosen in the binary expression
    - and no other alternative at a higher nesting depth was chosen.
    -}
    correct : ∀ (c : 2Config) (i : ℕ)
      → c (D ∙ i) ≡ true
      → (∀ (j : ℕ) → j < i → c (D ∙ j) ≡ false)
      → (fnoc c) D ≡ i
open FnocSpec

-- module Translate {ℓ₂} (S : Setoid ℓ₁ ℓ₂) where
module Translate (Carrier : Set ℓ₁) where
  -- open Setoid S renaming (refl to ≈-refl)
  _≈_ = _≡_
  open Eq.≡-Reasoning

  -- open import Data.Vec using (Vec; []; _∷_; fromList)

  {-| A dialect of binary choice calculus in which all data is in leaves. -}
  -- TODO: Write eliminator for NestedChoice given a variability language with choices.
  --       Then prove that the eliminator preserves semantics.
  data NestedChoice : Size → Set ℓ₁ where
    val : ∀ {ⅈ} → Carrier → NestedChoice ⅈ -- \ii
    chc : ∀ {ⅈ} → 2Choice I (NestedChoice ⅈ) → NestedChoice (↑ ⅈ)

  show-nested-choice : ∀ {ⅈ} → (Q → String) → (Carrier → String) → NestedChoice ⅈ → String
  show-nested-choice show-q show-carrier (val v) = show-carrier v
  show-nested-choice show-q show-carrier (chc c) =
    show-2choice
      (show-indexed-dimension show-q)
      (show-nested-choice show-q show-carrier)
      c

  ⟦_⟧ᵣ : ∀ {ⅈ} → NestedChoice ⅈ → 2Config → Carrier
  ⟦ val v ⟧ᵣ _ = v
  ⟦ chc γ ⟧ᵣ c = ⟦ ⟦ γ ⟧₂ c ⟧ᵣ c

  inc-dim : ∀ {ⅈ} → NestedChoice ⅈ → NestedChoice ⅈ
  inc-dim (val v) = val v
  -- TODO: Choices are always on the right-hand side, so it might be fine to simplify this function
  -- by applying inc-dim only to the right argument here.
  inc-dim (chc ((D ∙ i) ⟨ l , r ⟩)) = chc ((D ∙ suc i) ⟨ inc-dim l , inc-dim r ⟩)

  record Intermediate : Set ℓ₁ where
    constructor _≫_⟨_,_⟩
    field
      skip : ℕ
      name : Q
      head : Carrier
      tail : List Carrier

  ⟦_⟧ : Intermediate → NConfig → Carrier
  ⟦ skip ≫ D ⟨ e , es ⟩ ⟧ c = find-or-last (skip + c D) (e ∷ es)

  -- TODO: Do we actually need the name of the choice here?
  data _⟨_,_⟩⇝_ : Q → Carrier → List Carrier → 2Choice I (NestedChoice ∞) → Set ℓ₁
  infix 3 _⟨_,_⟩⇝_
  data _⟨_,_⟩⇝_ where
    base : ∀ {D : Q} {e : Carrier}
        ----------------------------------------
      → D ⟨ e , [] ⟩⇝ (D ∙ 0) ⟨ val e , val e ⟩

    step : ∀ {D : Q} {e₁ e₂ : Carrier} {es : List Carrier} {l r : NestedChoice ∞}
      →      D ⟨ e₂ , es ⟩⇝ (D ∙ 0) ⟨ l , r ⟩
        ---------------------------------------------------------------------------
      → D ⟨ e₁ , e₂ ∷ es ⟩⇝ (D ∙ 0) ⟨ val e₁ , inc-dim (chc ((D ∙ 0) ⟨ l , r ⟩)) ⟩
    {-
    Example execution trace
    step: D ⟨ 1 , 2 , 3 , 4 ⟩ ⇝ D0 ⟨ 1 , D1 ⟨ 2 , D2 ⟨ 3 , D3 ⟨ 4 , 4 ⟩ ⟩ ⟩ ⟩
    step:     D ⟨ 2 , 3 , 4 ⟩ ⇝          D0 ⟨ 2 , D1 ⟨ 3 , D2 ⟨ 4 , 4 ⟩ ⟩ ⟩
    step:         D ⟨ 3 , 4 ⟩ ⇝                   D0 ⟨ 3 , D1 ⟨ 4 , 4 ⟩ ⟩
    base:             D ⟨ 4 ⟩ ⇝                            D0 ⟨ 4 , 4 ⟩
    -}

  dim-constant : ∀ {D D'} {e es l r} {i}
    → D ⟨ e , es ⟩⇝ (D' ∙ i) ⟨ l , r ⟩
    → D ≡ D'
  dim-constant base = refl
  dim-constant (step _) = refl

  determinism-l : ∀ {D e es} {D₁ l₁ r₁} {D₂ l₂ r₂}
    → D ⟨ e , es ⟩⇝ (D₁ ∙ 0) ⟨ l₁ , r₁ ⟩
    → D ⟨ e , es ⟩⇝ (D₂ ∙ 0) ⟨ l₂ , r₂ ⟩
    → l₁ ≡ l₂
  determinism-l base base = refl
  determinism-l (step x) (step y) rewrite determinism-l x y = refl

  determinism-r : ∀ {D e es} {D₁ l₁ r₁} {D₂ l₂ r₂}
    → D ⟨ e , es ⟩⇝ (D₁ ∙ 0) ⟨ l₁ , r₁ ⟩
    → D ⟨ e , es ⟩⇝ (D₂ ∙ 0) ⟨ l₂ , r₂ ⟩
    → r₁ ≡ r₂
  determinism-r base base = refl
  determinism-r (step x) (step y) rewrite determinism-r x y | determinism-l x y = refl

  determinism : ∀ {D e es} {x y : 2Choice I (NestedChoice ∞)}
    → D ⟨ e , es ⟩⇝ x
    → D ⟨ e , es ⟩⇝ y
    → x ≡ y
  determinism base base = refl
  determinism (step ⇝x) (step ⇝y) rewrite determinism-r ⇝x ⇝y | determinism-l ⇝x ⇝y = refl

  Total' : Q → Carrier → List Carrier → Set ℓ₁
  Total' D e es = ∃[ x ] (D ⟨ e , es ⟩⇝ x)

  Total : NChoice Q Carrier → Set ℓ₁
  Total (D ⟨ e ∷ es ⟩) = Total' D e es

  -- Smart constructor for Totalₒ that does not require naming the expression explicitly.
  return : ∀ {D e es x}
    → D ⟨ e , es ⟩⇝ x
      ------------
    → Total (D ⟨ e ∷ es ⟩)
  return {x = x} ⇝x = x and ⇝x

  total : ∀ (D : Q) → (e : Carrier) (es : List Carrier)
    → Total' D e es
  total D e [] = return base
  total D e₁ (e₂ ∷ es) with total D e₂ es
  -- ... | ((.D ∙ 0) ⟨ .(val e₂) , .(val e₂) ⟩) and base = return (step base)
  -- ... | ((.D ∙ 0) ⟨ .(val e₂) , .(inc-dim (chc ((D ∙ 0) ⟨ _ , _ ⟩))) ⟩) and step ⇝e = return (step (step ⇝e))
  ... | (.D ∙ 0) ⟨ .(val e₂) , .(val e₂) ⟩ and base
    = (D ∙ 0) ⟨ val e₁ , chc ((D ∙ 1) ⟨ val e₂ , val e₂ ⟩) ⟩ and step base
  ... | (.D ∙ 0) ⟨ .(val e₂) , r ⟩ and step ⇝e
    = (D ∙ 0) ⟨ val e₁ , chc ((D ∙ 1) ⟨ val e₂ , inc-dim r ⟩) ⟩ and (step (step ⇝e))


  convert : NChoice Q Carrier → 2Choice I (NestedChoice ∞)
  convert (D ⟨ e ∷ es ⟩) = proj₁ (total D e es)

  module ISS = Data.IndexedSet (Eq.setoid Carrier)
  -- module ISS = Data.IndexedSet S
  open ISS using (_∈_at_; _⊆[_]_; _≅[_][_]_; ≐→≅[]; irrelevant-index-⊆; irrelevant-index-≅)
  open ISS.≅[]-Reasoning
  Preserved : NChoice Q Carrier → (NConfig → 2Config) → (2Config → NConfig) → Set ℓ₁
  Preserved (D ⟨ es ⟩) confi fnoci = ⟦ D ⟨ es ⟩ ⟧ₙ ≅[ confi ][ fnoci ] ⟦ chc (convert (D ⟨ es ⟩)) ⟧ᵣ

  module Preservation
    (confi : NConfig → 2Config)
    (fnoci : 2Config → NConfig)
    where
    open Data.List using (length)
    open import Data.Product using () renaming (_,_ to _and_)
    open import Util.AuxProofs using (if-idemp; if-idemp')
    open Eq.≡-Reasoning

    -- open Data.Nat using (_+_)
    open import Data.Nat.Properties using (≤-refl) --; m∸n≤m; m∸n≢0⇒n<m; 0∸n≡0; n∸n≡0; m≤n⇒m∸n≡0)

    flub : ∀ {n m}
      → n ≡ suc m
      → m < n
    flub refl = s≤s ≤-refl

    blar : ∀ {n m}
      → n ≡ suc m
      → 0 < n
    blar refl = s≤s z≤n

    -- preservation-⊆ : ∀ {D} {e₁ e₂ es} {l r}
    --   → ConfSpec D confi
    --   → D ⟨ e₁ , e₂ ∷ es ⟩⇝ (D ∙ 0) ⟨ val e₁ , inc-dim (chc ((D ∙ 0) ⟨ l , r ⟩)) ⟩
    --   → ⟦ D ⟨ e₁ ∷ e₂ ∷ es ⟩ ⟧ₙ ⊆[ confi ] ⟦ chc ((D ∙ 0) ⟨ val e₁ , inc-dim (chc ((D ∙ 0) ⟨ l , r ⟩)) ⟩) ⟧ᵣ
    -- preservation-⊆ conv x c = {!!}
    -- preservation-⊆ D e₁ e₂ es convi c with c D in cD≡x | total D e₂ es
    -- ... | zero | .((D ∙ 0) ⟨ val e₂ , val e₂ ⟩) and base rewrite select-n convi c cD≡x = refl
    -- ... | zero | .((D ∙ 0) ⟨ val e₂ , inc-dim (chc ((D ∙ 0) ⟨ _ , _ ⟩)) ⟩) and step snd rewrite select-n convi c cD≡x = refl
    -- ... | suc x | .((D ∙ 0) ⟨ val e₂ , val e₂ ⟩) and base rewrite deselect-<n convi c (blar cD≡x) =
    --   begin
    --     e₂
    --   ≡⟨ {!!} ⟩
    --     ⟦ ⟦ (D ∙ 1) ⟨ val e₂ , val e₂ ⟩ ⟧₂ (confi c) ⟧ᵣ (confi c)
    --   ∎
    -- preservation-⊆ D e₁ e₂ (e₃ ∷ es) convi c
    --   | suc x | .(D ∙ 0) ⟨ .(val e₂) , chc (.(D ∙ 1) ⟨ l , r ⟩ ) ⟩ and step snd rewrite deselect-<n convi c (blar cD≡x) =
    --     begin
    --       find-or-last x (e₂ ∷ e₃ ∷ es)
    --     ≡⟨ {!!} ⟩
    --       ⟦ ⟦ (D ∙ 1) ⟨ val e₂ , chc ((D ∙ 2) ⟨ inc-dim l , inc-dim r ⟩) ⟩ ⟧₂ (confi c) ⟧ᵣ (confi c)
    --     ∎
    --     where
    --       ind = preserves snd

      -- begin
      --   e₁
      -- ≡⟨ {!!} ⟩
      --   ⟦ chc (convert e) ⟧ᵣ (confi c)
      -- ≡⟨⟩
      --   ⟦ chc (convert e) ⟧ᵣ (confi c)
      -- ∎
    -- preservation-⊆ D _ _ [] c = ?
    --   Eq.cong
    --     (λ eq → ⟦ eq ⟧ᵣ (confi c))
    --     (Eq.sym
    --       (if-idemp (confi c (D ∙ 0))))
    -- preservation-⊆ (l ∷ r ∷ rs) c = {!!}

    -- preservation-⊇ : ∀ (es : List⁺ Carrier)
    --   → ⟦ chc (convert (D ⟨ es ⟩)) ⟧ᵣ ⊆[ fnoci ] ⟦ D ⟨ es ⟩ ⟧ₙ
    -- preservation-⊇ (_ ∷ []) c =
    --   Eq.cong
    --     (λ eq → ⟦ eq ⟧ᵣ c)
    --       (if-idemp (c (D ∙ 0)))
    -- preservation-⊇ (l ∷ r ∷ rs) c = {!!}

    preservation : ∀ {D} {e es} {l r}
      → ConfSpec D confi
      → FnocSpec D fnoci
      → D ⟨ e , es ⟩⇝ (D ∙ 0) ⟨ l , r ⟩
      → ⟦ D ⟨ e ∷ es ⟩ ⟧ₙ ≅[ confi ][ fnoci ] ⟦ chc ((D ∙ 0) ⟨ l , r ⟩) ⟧ᵣ
    preservation _ _ (base {D} {e}) =
      -- no matter how we configure our expression (or its translation),
      -- the result will always be e. this means, configurations are
      -- irrelevant here. hence, any translations of configurations may
      -- be used. hence, config and fnoci are fine.
      irrelevant-index-≅ e l-const r-const confi fnoci
      where
        l-const : ∀ c → ⟦ D ⟨ e ∷ [] ⟩ ⟧ₙ c ≈ e
        l-const c = refl --≈-refl

        r-const : ∀ c → ⟦ chc (convert (D ⟨ e ∷ [] ⟩)) ⟧ᵣ c ≈ e
        r-const c = Eq.cong (λ eq → ⟦ eq ⟧ᵣ c) (if-idemp (c (D ∙ 0)))
    proj₁ (preservation conv vnoc (step {D} {e₁} {e₂} {es} {l} {r} ⇝x)) c with c D in eq
    ... | zero rewrite select-n conv c eq = refl
    ... | suc x rewrite deselect-<n conv c (blar eq) =
      begin
      -- TODO: The following can never be true. So somewhere, we have a wrong assumption!
      --       We have to find it.
      --       Is it within deselect-<n?
      --       Or is the translation not preserving at all?
      --       Or are we applying the induction hypothesis wrongly?
        find-or-last x (e₂ ∷ es)
      -- ≡⟨⟩ ⟦ D ⟨ e₂ ∷ es ⟩ ⟧ₙ iff c D ≡ x
      ≡⟨ {!!} ⟩
        find-or-last (suc x) (e₂ ∷ es)
      ≡˘⟨ Eq.cong (λ a → find-or-last a (e₂ ∷ es)) eq ⟩
        find-or-last (c D) (e₂ ∷ es)
      ≡⟨⟩
        ⟦ D ⟨ e₂ ∷ es ⟩ ⟧ₙ c
      ≡⟨ hypot ⟩
        ⟦ ⟦ (D ∙ 0) ⟨ l , r ⟩ ⟧₂ (confi c) ⟧ᵣ (confi c)
      ≡⟨ {!!} ⟩
        ⟦ ⟦ (D ∙ 1) ⟨ inc-dim l , inc-dim r ⟩ ⟧₂ (confi c) ⟧ᵣ (confi c)
      ∎
      where
        hypot : ⟦ D ⟨ e₂ ∷ es ⟩ ⟧ₙ c ≡ ⟦ ⟦ (D ∙ 0) ⟨ l , r ⟩ ⟧₂ (confi c) ⟧ᵣ (confi c)
        hypot = proj₁ (preservation conv vnoc ⇝x) c
    proj₂ (preservation conv vnoc (step {D} {e₁} {e₂} {es} {l} {r} ⇝x)) c = {!!}
      -- ≅[]-begin
      --   ⟦ D ⟨ e₁ ∷ e₂ ∷ es ⟩ ⟧ₙ
      -- ≅[]⟨ {!!} ⟩
      --   (λ c → ⟦ ⟦ (D ∙ 0) ⟨ val e₁ , chc ((D ∙ 1) ⟨ inc-dim l , inc-dim r ⟩) ⟩ ⟧₂ c ⟧ᵣ c)
      -- ≅[]-∎

    -- preservation _ (D ⟨ e ∷ [] ⟩) =
    -- preservation (D ⟨ e₁ ∷ e₂ ∷ es ⟩) = ? --preservation-⊆ D e₁ e₂ es {!!} and {!!}

    -- -- convert-preserves-l : ∀ (e : L₁ A) (es : List (L₁ A)) (c : NConfig)
    -- --   → ConfSpec D confi
    -- --   -- → ConfSpec D (length es) confi
    -- --   → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) (e ∷ es)
    -- --   →   Choice-Semantics       VL₁ (D ⟨ e ∷ es ⟩) c
    -- --     ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ es ⟩)) (confi c)
    -- convert-preserves-l : ∀ (e : Carrier) (es : List Carrier) (c : NConfig)
    --   → ConfSpec D confi
    --   → (max : ℕ)
    --   → (i : ℕ)
    --   -- → i + length es ≡ max
    --   → length es ≤ max
    --   → max ≤ i + length es
    --   -- → max ∸ length es ≤ i
    --   → c D ≡ i
    --   →   ⟦ find-or-last (i ∸ (max ∸ length es)) (e ∷ es) ⟧ₙ c
    --     ≈ ⟦ unroll max D (e ∷ fromList es) ⟧₂ (confi c)
    --     -- ≡ BinaryChoice-Semantics VL₂ (unroll (length es) D (e ∷ fromList es)) (confi c)

    -- convert-preserves-l-base : ∀ (e : Carrier) (c : NConfig)
    --   →   ⟦ D ⟨ e ∷ [] ⟩ ⟧ₙ c
    --     ≡ ⟦ convert (D ⟨ e ∷ [] ⟩) ⟧₂ (confi c)
    -- convert-preserves-l-base e c =
    --   begin
    --     ⟦ D ⟨ e ∷ [] ⟩ ⟧ₙ c
    --   ≡⟨⟩
    --     ⟦ e ⟧ₙ c
    --   ≡⟨⟩
    --     ⟦ e ⟧₂ (confi c)
    --   ≡⟨ Eq.cong
    --        (λ eq → ⟦ eq ⟧₂ (confi c))
    --        (Eq.sym
    --          (if-idemp ((confi c) (D ∙ 0)))) ⟩
    --     ⟦ if ((confi c) (D ∙ 0)) then e else e ⟧₂ (confi c)
    --   ≡⟨⟩
    --     ⟦ convert (D ⟨ e ∷ [] ⟩) ⟧₂ (confi c)
    --   ∎

    -- convert-preserves-l-base' : ∀ (e : Carrier) (c : NConfig)
    --   → (max : ℕ)
    --   →   ⟦ D ⟨ e ∷ [] ⟩ ⟧ₙ c
    --     ≡ ⟦ unroll max D (e ∷ []) ⟧₂ (confi c)
    -- convert-preserves-l-base' e c max =
    --   begin
    --     ⟦ D ⟨ e ∷ [] ⟩ ⟧ₙ c
    --   ≡⟨⟩
    --     e
    --   ≡˘⟨ if-idemp ((confi c) (D ∙ max)) ⟩
    --     (if ((confi c) (D ∙ max)) then e else e)
    --   ≡⟨⟩
    --     ⟦ unroll max D (e ∷ []) ⟧₂ (confi c)
    --   ∎

    -- convert-preserves-l-step : ∀ (l r : Carrier) (es : List Carrier) (c : NConfig)
    --    → (conv : ConfSpec D confi)
    --    -- → ConfSpec D (suc (length es)) confi
    --    → (max : ℕ)
    --    -- → length (r ∷ es) ≤ max
    --    → (i : ℕ)
    --    -- → max ≤ i + length (r ∷ es)
    --    → (n≤max : length (r ∷ es) ≤ max)
    --    → (max≤i+n : max ≤ i + length (r ∷ es))
    --    → (cD≡i : c D ≡ i)
    --    -- →   Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
    --    →   ⟦ find-or-last (i ∸ (max ∸ length (r ∷ es))) (l ∷ r ∷ es) ⟧ₙ c
    --      -- ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
    --      ≡ ⟦ unroll max D (l ∷ fromList (r ∷ es)) ⟧₂ (confi c)
    -- convert-preserves-l-step l r es c conv (suc max) zero (s≤s n≤max) (s≤s max≤i+n) cD≡i = ?
    --   -- begin
    --   --   (find-or-last (zero ∸ (max ∸ n)) (l ∷ r ∷ es))
    --   -- ≡⟨ 0∸n≡0 (max ∸ n) ⟩
    --   --   l
    --   -- ≡˘⟨ select-n conv c max∸n≡cD ⟩
    --   --   (if (confi c) (D ∙ (max ∸ n)) then l else tail)
    --   -- ∎
    --   where n = length es
    --         tail = unroll (suc max) D (r ∷ fromList es)

    --         max∸n≡0 : max ∸ n ≡ 0
    --         max∸n≡0 = m≤n⇒m∸n≡0 max≤i+n

    --         max∸n≡cD : max ∸ n ≡ c D
    --         max∸n≡cD = Eq.trans max∸n≡0 (Eq.sym cD≡i)
    -- convert-preserves-l-step l r es c conv (suc max) (suc i) (s≤s n≤max) (s≤s max≤i+n) cD≡i with max ∸ (length es) in eq
    -- ... | zero = ?
    --   -- begin
    --   --   ⟦ find-or-last i (r ∷ es) ⟧ₙ c
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ find-or-last x (r ∷ es) ⟧ₙ c)
    --   --      lh ⟩
    --   --   -- ⟦ find-or-last (i ∸ (max ∸ length es)) (r ∷ es) ⟧ₙ c
    --   --   ⟦ find-or-last (suc i ∸ (suc max ∸ n)) (r ∷ es) ⟧ₙ c
    --   -- -- ≡⟨ {!!} ⟩
    --   -- ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ es≡tes) (suc max) (suc i) n≤1+m 1+m≤1+i+n cD≡i ⟩
    --   -- -- ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ es≡tes) (suc max) (suc i) ? cD≡i ⟩
    --   --   ⟦ unroll (suc max) D (r ∷ fromList es) ⟧₂ (confi c)
    --   -- ≡⟨⟩
    --   --   ⟦ tail ⟧₂ (confi c)
    --   -- -- ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    --   --   -- ⟦ mkChoice tail ⟧₂ (confi c)
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ if x then l else tail ⟧₂ (confi c))
    --   --      (Eq.sym (deselect-<n conv c 0<cD)) ⟩
    --   --   ⟦ if (confi c) (D ∙ zero) then l else tail ⟧₂ (confi c)
    --   -- ∎
    --   where tail = unroll (suc max) D (r ∷ fromList es)
    --         n    = length es

    --         0<cD : zero < c D
    --         0<cD rewrite cD≡i = s≤s z≤n

    --         max∸n≡0 : max ∸ n ≡ 0
    --         max∸n≡0 = eq

    --         m≤n : max ≤ n
    --         m≤n = {!!} -- follows from max∸n≡0

    --         m≡n : max ≡ n
    --         m≡n = {!!} -- from m≤n and n≤max

    --         [1+m]∸n≡1 : suc max ∸ n ≡ 1
    --         [1+m]∸n≡1 rewrite m≡n = {!!} -- follows from 1 + x - x = x

    --         lh : i ≡ suc i ∸ (suc max ∸ n)
    --         lh rewrite [1+m]∸n≡1 = refl

    --         n≤1+m : n ≤ suc max
    --         n≤1+m rewrite m≡n = {!!} -- follows from x ≤ 1 + x

    --         1+m≤1+i+n : suc max ≤ suc (i + n)
    --         1+m≤1+i+n rewrite m≡n = s≤s {!!} -- follows from x ≤ y + x
    -- ... | suc d = ? -- maybe split on i here?
    --   -- begin
    --   --   ⟦ find-or-last (i ∸ d) (l ∷ r ∷ es) ⟧ₙ c
    --   -- ≡⟨ {!!} ⟩
    --   --   ⟦ if (confi c) (D ∙ suc d) then l else tail ⟧₂ (confi c)
    --   -- ∎
    --   where tail = unroll (suc max) D (r ∷ fromList es)
    --         n    = length es

    --         m∸n≡1+d : max ∸ n ≡ suc d
    --         m∸n≡1+d = eq

    --         n<m : n < max
    --         n<m = {!!} -- follows from m∸n≡1+d

    --         m∸n≤i : max ∸ n ≤ i
    --         m∸n≤i = {!!} -- I think, we cannot prove this.

    --         0<m∸n : 0 < max ∸ n
    --         0<m∸n = {!!} -- follows from m∸n≡1+d

    --         1+d<cD : suc d < c D
    --         1+d<cD rewrite cD≡i | Eq.sym m∸n≡1+d = s≤s m∸n≤i
    --   -- begin
    --   --   -- Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
    --   -- -- ≡⟨⟩
    --   --   -- ⟦ find-or-last (c D) (l ∷ r ∷ es) ⟧₁ c
    --   -- -- ≡⟨ Eq.cong
    --   --      -- (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
    --   --      -- cD≡i ⟩
    --   --   ⟦ find-or-last (suc i ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
    --   -- -- ≡⟨⟩
    --   --   -- ⟦ find-or-last i (r ∷ es) ⟧₁ c
    --   -- ≡⟨ {!!} ⟩ -- {!convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max ? (suc i) cD≡i!} ⟩
    --   -- --   BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
    --   -- -- ≡⟨⟩
    --   -- --   BinaryChoice-Semantics VL₂ tail (confi c)
    --   -- -- ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    --   --   ⟦ mkChoice tail ⟧₂ (confi c)
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    --   --      (Eq.sym (deselect-<n conv c {!!})) ⟩
    --   --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else mkChoice tail ⟧₂ (confi c)
    --   -- ∎
    --   -- where n = length es
    --   --       tail = unroll (suc max) D (r ∷ fromList es)
    --   -- begin
    --   --   ⟦ find-or-last (zero ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
    --   --      (0∸n≡0 (max ∸ n)) ⟩
    --   --   ⟦ l ⟧₁ c
    --   -- ≡⟨ l≡tl ⟩
    --   --   ⟦ t l ⟧₂ (confi c)
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ if x then t l else tail ⟧₂ (confi c))
    --   --      (Eq.sym (select-n conv c max∸n≡cD)) ⟩
    --   --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else tail ⟧₂ (confi c)
    --   -- ∎
    --   -- where n = suc (length es)
    --   --       tail = mkChoice (unroll max D (r ∷ fromList es))

    --   --       max∸n≡0 : max ∸ n ≡ 0
    --   --       max∸n≡0 = m≤n⇒m∸n≡0 max≤n

    --   --       max∸n≡cD : max ∸ n ≡ c D
    --   --       max∸n≡cD = Eq.trans max∸n≡0 (Eq.sym cD≡i)
    --   --       -- pick : suc n ∸ c D ≡ suc n
    --   --       -- pick rewrite cD≡i = refl
    -- -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ es≡tes) zero (suc i) n≤max z≤n cD≡i =
    -- --   begin
    -- --     ⟦ find-or-last i (r ∷ es) ⟧₁ c
    -- --   ≡⟨ {!!} ⟩
    -- --   -- ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max (suc i) asd cD≡i ⟩
    -- --     BinaryChoice-Semantics VL₂ (unroll zero D (r ∷ fromList es)) (confi c)
    -- --   ≡⟨⟩
    -- --     BinaryChoice-Semantics VL₂ tail (confi c)
    -- --   ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    -- --     ⟦ mkChoice tail ⟧₂ (confi c)
    -- --   ≡⟨ Eq.cong
    -- --        (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    -- --        (Eq.sym (deselect-<n conv c {! doable!})) ⟩
    -- --     ⟦ if (confi c) (D ∙ zero) then t l else mkChoice tail ⟧₂ (confi c)
    -- --   ∎
    -- --   where tail = unroll zero D (r ∷ fromList es)
    -- -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ es≡tes) (suc max) (suc i) max∸n≤i cD≡i = {!!}
    -- -- convert-preserves-l-step l r es c conv (l≡tl ∷ r≡tr ∷ hypot-es) max (suc i) max≤1+i+n cD≡i with max ∸ length (r ∷ es) in eq
    -- -- ... | zero =
    -- --   begin
    -- --     ⟦ find-or-last i (r ∷ es) ⟧₁ c
    -- --   ≡⟨ {!!} ⟩
    -- --     ⟦ find-or-last (suc i ∸ (max ∸ length es)) (r ∷ es) ⟧₁ c
    -- --   ≡⟨ convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max (suc i) asd cD≡i ⟩
    -- --     BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
    -- --   ≡⟨⟩
    -- --     BinaryChoice-Semantics VL₂ tail (confi c)
    -- --   ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    -- --     ⟦ mkChoice tail ⟧₂ (confi c)
    -- --   ≡⟨ Eq.cong
    -- --        (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    -- --        (Eq.sym (deselect-<n conv c {! doable!})) ⟩
    -- --     ⟦ if (confi c) (D ∙ zero) then t l else mkChoice tail ⟧₂ (confi c)
    -- --   ∎
    -- --   where tail = unroll max D (r ∷ fromList es)
    -- --         asd : max ∸ length es ≤ suc i
    -- --         asd = {!!}

    -- -- ... | suc x = {!!}
    --   -- begin
    --   --   -- Choice-Semantics VL₁ (D ⟨ l ∷ r ∷ es ⟩) c
    --   -- -- ≡⟨⟩
    --   --   -- ⟦ find-or-last (c D) (l ∷ r ∷ es) ⟧₁ c
    --   -- -- ≡⟨ Eq.cong
    --   --      -- (λ x → ⟦ find-or-last x (l ∷ r ∷ es) ⟧₁ c)
    --   --      -- cD≡i ⟩
    --   --   ⟦ find-or-last ((suc i) ∸ (max ∸ n)) (l ∷ r ∷ es) ⟧₁ c
    --   -- -- ≡⟨⟩
    --   --   -- ⟦ find-or-last i (r ∷ es) ⟧₁ c
    --   -- ≡⟨ {!!} ⟩ -- {!convert-preserves-l r es c conv (r≡tr ∷ hypot-es) max ? (suc i) cD≡i!} ⟩
    --   --   BinaryChoice-Semantics VL₂ (unroll max D (r ∷ fromList es)) (confi c)
    --   -- ≡⟨⟩
    --   --   BinaryChoice-Semantics VL₂ tail (confi c)
    --   -- ≡⟨ Eq.sym (mkChoice-preserves tail (confi c)) ⟩
    --   --   ⟦ mkChoice tail ⟧₂ (confi c)
    --   -- ≡⟨ Eq.cong
    --   --      (λ x → ⟦ if x then t l else mkChoice tail ⟧₂ (confi c))
    --   --      (Eq.sym (deselect-<n conv c {!!})) ⟩
    --   --   ⟦ if (confi c) (D ∙ (max ∸ n)) then t l else mkChoice tail ⟧₂ (confi c)
    --   -- ∎
    --   -- where n = length (r ∷ es)
    --   --       tail = unroll max D (r ∷ fromList es)

    --   --       -- TODO: Move to aux proofs
    --   --       asdf : ∀ {n m} → suc (n ∸ m) ≤ suc n
    --   --       asdf {zero} {zero} = s≤s z≤n
    --   --       asdf {zero} {suc _} = s≤s z≤n
    --   --       asdf {suc n} {zero} = ≤-refl
    --   --       asdf {suc n} {suc m} = s≤s (m∸n≤m (suc n) (suc m))

    --         -- pick : max ∸ n < c D
    --         -- pick rewrite cD≡i = s≤s {!!}

    -- convert-preserves-l e [] c _ max _ _ _ _ = convert-preserves-l-base' e c max
    -- convert-preserves-l l (r ∷ es) c conv max i asd eq cD≡i = convert-preserves-l-step l r es c conv max i asd eq cD≡i

    -- -- convert-preserves-l :
    -- --     ConfSpec D confi
    -- --   → (alts : List⁺ (L₁ A))
    -- --   → (c : NConfig)
    -- --   → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) alts
    -- --   →   Choice-Semantics       VL₁ (D ⟨ alts ⟩) c
    -- --     ≡ BinaryChoice-Semantics VL₂ (unroll D alts zero) (confi c)
    -- -- convert-preserves-l conv (e ∷ []) c (e≡tx ∷ []) =
    -- --   begin
    -- --     Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
    -- --   ≡⟨⟩
    -- --     ⟦ e ⟧₁ c
    -- --   ≡⟨ e≡tx ⟩
    -- --     ⟦ t e ⟧₂ (confi c)
    -- --   ≡⟨ Eq.cong
    -- --        (λ eq → ⟦ eq ⟧₂ (confi c))
    -- --        (Eq.sym
    -- --          (if-idemp ((confi c) (D ∙ 0)))) ⟩
    -- --     ⟦ if ((confi c) (D ∙ 0)) then (t e) else (t e) ⟧₂ (confi c)
    -- --   ≡⟨⟩
    -- --     BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ [] ⟩)) (confi c)
    -- --   ∎
    -- -- convert-preserves-l conv (l ∷ r ∷ es) c (l≡tl ∷ r≡tr ∷ hypot-es) with c D in eq
    -- -- ... | zero  =
    -- --   begin
    -- --     ⟦ l ⟧₁ c
    -- --   ≡⟨ l≡tl ⟩
    -- --     ⟦ t l ⟧₂ (confi c)
    -- --   ≡⟨⟩
    -- --     ⟦ if true then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    -- --   ≡⟨ Eq.cong
    -- --        (λ x → ⟦ if x then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c))
    -- --        (Eq.sym (select-n conv c 0 (Eq.sym eq))) ⟩
    -- --     ⟦ if (confi c) (D ∙ 0) then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    -- --   ≡⟨⟩
    -- --     BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
    -- --   ∎
    -- -- ... | suc n =
    -- --   begin
    -- --     ⟦ find-or-last n (r ∷ es) ⟧₁ c
    -- --   -- ≡⟨ {!!} ⟩
    -- --     -- ⟦ ⟧₂
    -- --   -- ≡⟨⟩
    -- --     -- BinaryChoice-Semantics VL₂ (unroll D (r ∷ es) zero) (confi c)
    -- --   ≡⟨ {!!} ⟩
    -- --     BinaryChoice-Semantics VL₂ (unroll D (r ∷ es) 1) (confi c)
    -- --   ≡⟨ Eq.sym (mkChoice-preserves (unroll D (r ∷ es) 1) (confi c)) ⟩
    -- --     ⟦ mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    -- --   ≡⟨⟩
    -- --     ⟦ if false then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    -- --   ≡⟨ Eq.cong
    -- --        (λ x → ⟦ if x then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c))
    -- --        (Eq.sym (deselect-<n conv c 0 {!!})) ⟩
    -- --     ⟦ if (confi c) (D ∙ 0) then t l else mkChoice (unroll D (r ∷ es) 1) ⟧₂ (confi c)
    -- --   ≡⟨⟩
    -- --     BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
    -- --   ∎

    -- convert-preserves : ∀ (alts : List⁺ Carrier) →
    --       ⟦ D ⟨ alts ⟩ ⟧ₙ
    --     ≅ ⟦ convert (D ⟨ alts ⟩) ⟧₂
    -- convert-preserves = {!!}

    -- L₂-has-choices-syntactically : BinaryChoice I ∈ₛ L₂
    -- L₂-has-choices-syntactically = make L₂-has-choices

    -- mkChoice : BinaryChoice I L₂ A → L₂ A
    -- mkChoice = cons L₂-has-choices-syntactically

    -- mkChoice-preserves : ∀ (c : BinaryChoice I L₂ A) → ⟦ mkChoice c ⟧₂ ≗ BinaryChoice-Semantics VL₂ c
    -- mkChoice-preserves = preservation L₂-has-choices
