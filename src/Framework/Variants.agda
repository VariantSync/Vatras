{-# OPTIONS --allow-unsolved-metas #-}

module Framework.Variants where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Function using (id; _∘_; flip)
open import Size using (Size; ↑_; ∞)

open import Framework.Definitions using (𝕍; 𝔸; atoms)
open import Framework.VariabilityLanguage

open import Data.EqIndexedSet

data GrulerVariant : 𝕍 where
  ε     : ∀ {A : 𝔸} → GrulerVariant A
  asset : ∀ {A : 𝔸} (a : atoms A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

data Rose : Size → 𝕍 where
  _-<_>- : ∀ {i} {A : 𝔸} → atoms A → List (Rose i A) → Rose (↑ i) A

rose-leaf : ∀ {A : 𝔸} → atoms A → Rose ∞ A
rose-leaf {A} a = a -< [] >-

-- Variants are also variability languages
Variant-is-VL : ∀ (V : 𝕍) → VariabilityLanguage V
Variant-is-VL V = ⟪ V , ⊤ , (λ e c → e) ⟫

open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality as Peq using (_≡_; _≗_; refl)
open Peq.≡-Reasoning

children-equality : ∀ {A : 𝔸} {a₁ a₂ : atoms A} {cs₁ cs₂ : List (Rose ∞ A)} → a₁ -< cs₁ >- ≡ a₂ -< cs₂ >- → cs₁ ≡ cs₂
children-equality refl = refl

GrulerVL : VariabilityLanguage GrulerVariant
GrulerVL = Variant-is-VL GrulerVariant

RoseVL : VariabilityLanguage (Rose ∞)
RoseVL = Variant-is-VL (Rose ∞)

open import Data.String using (String; _++_; intersperse)
show-rose : ∀ {i} {A} → (atoms A → String) → Rose i A → String
show-rose show-a (a -< [] >-) = show-a a
show-rose show-a (a -< es@(_ ∷ _) >-) = show-a a ++ "-<" ++ (intersperse ", " (map (show-rose show-a) es)) ++ ">-"


-- Variants can be encoded into other variability language.
-- The result is an expression which cannot be configured
-- (i.e., configurations don't matter because there is only
-- a single variant anyway).

open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler

VariantEncoder : ∀ (V : 𝕍) (Γ : VariabilityLanguage V) → Set₁
VariantEncoder V Γ = LanguageCompiler (Variant-is-VL V) Γ


module _ (V : 𝕍) (A : 𝔸) {Γ : VariabilityLanguage V} (encoder : VariantEncoder V Γ) where
  open import Data.EqIndexedSet

  private
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics (Variant-is-VL V)

  encoded-variant-is-singleton-set :
    ∀ (v : V A) → Singleton ⟦ compile encoder v ⟧
  encoded-variant-is-singleton-set v = v , λ c → proj₂ (preserves encoder v) c

  encode-idemp : ∀ (c : Config Γ) (v : V A)
    → ⟦ compile encoder v ⟧ c ≡ v
  encode-idemp c v =
    begin
      ⟦ compile encoder v ⟧ c
    ≡⟨ irrelevant-index (encoded-variant-is-singleton-set v) ⟩
      ⟦ compile encoder v ⟧ (conf encoder v tt)
    ≡⟨ proj₁ (preserves encoder v) tt ⟨
      ⟦ v ⟧ᵥ tt
    ≡⟨⟩
      v
    ∎
