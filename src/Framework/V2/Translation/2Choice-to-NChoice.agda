module Framework.V2.Translation.2Choice-to-NChoice where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

open import Framework.V2.Definitions
open import Framework.V2.Variants using (VariantSetoid)
open import Framework.V2.V1Compat
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

module 2→N-Choice {F : 𝔽} where
  {-|
  ConfSpec and FnocSpec define the requirements we have on translated configurations
  to prove preservation of the conversion from binary to n-ary choices.
  -}
  record ConfSpec (f : F) (conf : Config F Bool → Config F ℕ) : Set where
    field
      false→1 : ∀ (c : Config F Bool)
        → c f ≡ false
        → (conf c) f ≡ 1
      true→0 : ∀ (c : Config F Bool)
        → c f ≡ true
        → (conf c) f ≡ 0
  open ConfSpec

  record FnocSpec (f : F) (fnoc : Config F ℕ → Config F Bool) : Set where
    field
      suc→false : ∀ {n} (c : Config F ℕ)
        → c f ≡ suc n
        → (fnoc c) f ≡ false
      zero→true : ∀ (c : Config F ℕ)
        → c f ≡ zero
        → (fnoc c) f ≡ true
  open FnocSpec

  default-conf : Config F Bool → Config F ℕ
  (default-conf cb) f with cb f
  ... | false = 1
  ... | true  = 0

  default-fnoc : Config F ℕ → Config F Bool
  (default-fnoc cn) f with cn f
  ... | zero    = true
  ... | (suc _) = false

  default-conf-satisfies-spec : ∀ (f : F) → ConfSpec f default-conf
  false→1 (default-conf-satisfies-spec f) c cf≡false rewrite cf≡false = refl
  true→0  (default-conf-satisfies-spec f) c cf≡true  rewrite cf≡true  = refl

  default-fnoc-satisfies-spec : ∀ (f : F) → FnocSpec f default-fnoc
  suc→false (default-fnoc-satisfies-spec f) c cf≡suc  rewrite cf≡suc  = refl
  zero→true (default-fnoc-satisfies-spec f) c cf≡zero rewrite cf≡zero = refl

  module Translate {V}
    (VL₁ : VariabilityLanguage V F Bool)
    (VL₂ : VariabilityLanguage V F ℕ)
    (t : expression-set VL₁ A → expression-set VL₂ A)
    where
    private
      L₁   = expression-set VL₁
      L₂   = expression-set VL₂
      ⟦_⟧₁ = semantics VL₁ {A}
      ⟦_⟧₂ = semantics VL₂ {A}

    convert : BinaryChoice F L₁ A → Choice F L₂ A
    convert (D ⟨ l , r ⟩) = D ⟨ t l ∷ t r ∷ [] ⟩

    module Preservation
      (confi : Config F Bool → Config F ℕ)
      (fnoci : Config F ℕ → Config F Bool)
      (D : F)
      (l r : expression-set VL₁ A)
      where
      open Data.IndexedSet (VariantSetoid V A) using (⊆-by-index-translation) renaming (_≅_ to _≋_)

      private
        2Config = Config F Bool
        NConfig = Config F ℕ

      preserves-conf :
          ConfSpec D confi
        → Conf-Preserves VL₁ VL₂ l (t l) confi
        → Conf-Preserves VL₁ VL₂ r (t r) confi
        → (c : 2Config)
        →   BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩) c
          ≡ Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩)) (confi c)
      preserves-conf conv t-l t-r c with c D in eq
      ... | false rewrite false→1 conv c eq = t-r c
      ... | true  rewrite true→0  conv c eq = t-l c

      preserves-fnoc :
          FnocSpec D fnoci
        → Fnoc-Preserves VL₁ VL₂ l (t l) fnoci
        → Fnoc-Preserves VL₁ VL₂ r (t r) fnoci
        → (c : NConfig)
        →   Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩)) c
          ≡ BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩) (fnoci c)
      preserves-fnoc vnoc t-l t-r c with c D in eq
      ... | zero  rewrite zero→true vnoc c eq = t-l c
      ... | suc _ rewrite suc→false vnoc c eq = t-r c

      convert-preserves :
        ∀ (conv : ConfSpec D confi)
        → (vnoc : FnocSpec D fnoci)
        -- boilerplaty induction hypothesis
        → Conf-Preserves VL₁ VL₂ l (t l) confi
        → Fnoc-Preserves VL₁ VL₂ l (t l) fnoci
        → Conf-Preserves VL₁ VL₂ r (t r) confi
        → Fnoc-Preserves VL₁ VL₂ r (t r) fnoci
        →   BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩)
          ≋ Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩))
      convert-preserves conv vnoc conf-l fnoc-l conf-r fnoc-r =
            ⊆-by-index-translation confi (preserves-conf conv conf-l conf-r)
        and ⊆-by-index-translation fnoci (preserves-fnoc vnoc fnoc-l fnoc-r)
